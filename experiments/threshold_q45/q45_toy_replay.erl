%% Test-only replay of trusted Python P0 toy-BFV vectors through the P1 actor.
%% The evaluator retrieves a fixture for the exact input list. The combiner
%% reconstructs in Erlang from the bytes admitted by the actor.
-module(q45_toy_replay).
-export([run/1, run_p2b/1]).

-define(PARTIES, [1, 2, 3, 4, 5]).
-define(Q, ((1 bsl 127) - 1)).
-define(N, 32).
-define(POLY_BYTES, (?N * 16)).

run(Path) ->
    {ok, Contents} = file:read_file(Path),
    Rows = binary:split(Contents, <<"\n">>, [global, trim]),
    Ids = [replay_row(Row) || Row <- Rows],
    Expected = [{Seed, Mask, Omitted} || Seed <- [16#45, 16#1234, 16#7, 16#63],
                Mask <- lists:seq(0, 31), Omitted <- ?PARTIES],
    true = lists:sort(Ids) =:= lists:sort(Expected),
    io:format("P0/P1 toy replay: ~B/~B seed/input/quorum cases; 4 malformed payload probes rejected~n",
              [length(Ids), length(Expected)]).

%% Separate P2b characterization: the same actor also completes with a
%% canonical dishonest partial. This is evidence of a missing verification
%% obligation, not an acceptance gate for release.
run_p2b(Path) ->
    {ok, Contents} = file:read_file(Path),
    Rows = binary:split(Contents, <<"\n">>, [global, trim]),
    Ids = [replay_row(Row) || Row <- Rows],
    Expected = [{Seed, Mask, Omitted} || Seed <- [16#45, 16#1234, 16#7, 16#63],
                Mask <- lists:seq(0, 31), Omitted <- ?PARTIES],
    true = lists:sort(Ids) =:= lists:sort(Expected),
    lists:foreach(fun replay_poisoned_row/1, Rows),
    io:format("P2b/P1: 640 honest cases; 640 canonical bit-flip attacks completed; "
              "640 small-offset attacks completed; 4 malformed probes aborted~n").

replay_poisoned_row(Row) ->
    [Seed, Mask, Omitted, Bit | Blobs] = binary:split(Row, <<"\t">>, [global]),
    [C1, C2, C3, C4, C5, Ciphertext, D1, D2, D3, D4] =
        [binary:decode_hex(Blob) || Blob <- Blobs],
    Inputs = [C1, C2, C3, C4, C5],
    S = ?PARTIES -- [binary_to_integer(Omitted)],
    Original = binary_to_integer(Bit),
    Sid = iolist_to_binary(lists:join(<<"/">>, [<<"p2b-attack">>, Seed, Mask, Omitted])),
    % Each modification is public ring arithmetic on an admitted share. It
    % needs neither a secret key nor a smudging oracle.
    lists:foreach(fun({Suffix, Offset, Expected}) ->
        Altered = offset_constant(D1, Offset),
        with_frozen(<<Sid/binary, Suffix/binary>>, Inputs, Ciphertext, S,
            fun(Pid, Binding) ->
                ActiveSid = <<Sid/binary, Suffix/binary>>,
                submit_parts(Pid, ActiveSid, Binding, S, [Altered, D2, D3, D4]),
                {error, inconsistent_result} = send(Pid, ActiveSid, {result, Binding, Expected bxor 1}),
                ok = send(Pid, ActiveSid, {result, Binding, Expected}),
                {complete, #{result := Expected}} = sys:get_state(Pid)
            end)
    end, [{<<"/flip">>, ?Q div 2, Original bxor 1},
          {<<"/small">>, 1 bsl 80, Original}]).

offset_constant(Part, Offset) ->
    [Head | Tail] = polynomial(Part),
    Changed = (Head + Offset) rem ?Q,
    iolist_to_binary([<<A:128/big>> || A <- [Changed | Tail]]).

replay_row(Row) ->
    [Seed, Mask, Omitted, Bit | Blobs] = binary:split(Row, <<"\t">>, [global]),
    [C1, C2, C3, C4, C5, Evaluated, D1, D2, D3, D4] =
        [binary:decode_hex(Blob) || Blob <- Blobs],
    I = binary_to_integer(Omitted),
    S = ?PARTIES -- [I],
    Sid = iolist_to_binary(lists:join(<<"/">>, [Seed, Mask, Omitted])),
    Fixture = {[C1, C2, C3, C4, C5], Evaluated, S, [D1, D2, D3, D4], binary_to_integer(Bit)},
    try
        replay(Sid, Fixture),
        case {Mask, I} of
            {<<"0">>, 5} -> reject_malformed(<<Sid/binary, "/malformed">>, Fixture);
            _ -> ok
        end
    catch
        Class:Reason:Stack -> erlang:raise(Class, {toy_replay, Sid, Reason}, Stack)
    end,
    {binary_to_integer(Seed), binary_to_integer(Mask), I}.

replay(Sid, {Inputs, Ciphertext, S, Parts, Bit}) ->
    with_frozen(Sid, Inputs, Ciphertext, S, fun(Pid, {_, Digest, _} = Binding) ->
        [First | _] = S,
        [FirstPart | _] = Parts,
        <<Head, Rest/binary>> = Ciphertext,
        Altered = <<(Head bxor 1), Rest/binary>>,
        {error, invalid_event} = send(Pid, Sid, {partial, First, {Altered, Digest, S}, FirstPart}),
        submit_parts(Pid, Sid, Binding, S, Parts),
        {error, inconsistent_result} = send(Pid, Sid, {result, Binding, Bit bxor 1}),
        ok = send(Pid, Sid, {result, Binding, Bit}),
        {complete, #{result := Bit}} = sys:get_state(Pid),
        {error, terminal} = send(Pid, Sid, {result, Binding, Bit})
    end).

reject_malformed(Sid, {Inputs, Ciphertext, S, [_ | Tail], Bit}) ->
    with_frozen(Sid, Inputs, Ciphertext, S, fun(Pid, Binding) ->
        % P1 admits the opaque envelope. The test combiner rejects its encoding.
        submit_parts(Pid, Sid, Binding, S, [<<1>> | Tail]),
        {error, combiner_failed} = send(Pid, Sid, {result, Binding, Bit}),
        {aborted, Data} = sys:get_state(Pid),
        false = maps:is_key(result, Data)
    end).

with_frozen(Sid, Inputs, Ciphertext, S, Test) ->
    Evaluate = fun(Ordered) when Ordered =:= Inputs -> Ciphertext end,
    {ok, Pid} = q45_ceremony:start_link(Sid, 10000, Evaluate, fun combine/3),
    try
        lists:foreach(fun({I, C}) -> ok = send(Pid, Sid, {input, I, C}) end,
                      lists:reverse(lists:zip(?PARTIES, Inputs))),
        Digest = crypto:hash(sha256, Ciphertext),
        lists:foreach(fun(I) -> ok = send(Pid, Sid, {seal, I, Digest}) end, ?PARTIES),
        lists:foreach(fun(I) -> ok = send(Pid, Sid, {commit, I, Digest}) end, lists:reverse(S)),
        Test(Pid, {Ciphertext, Digest, S})
    after
        gen_statem:stop(Pid)
    end.

submit_parts(Pid, Sid, Binding, S, Parts) ->
    lists:foreach(fun({I, D}) -> ok = send(Pid, Sid, {partial, I, Binding, D}) end,
                  lists:reverse(lists:zip(S, Parts))).

send(Pid, Sid, Event) -> q45_ceremony:submit(Pid, Sid, Event).

combine(<<C0:?POLY_BYTES/binary, C1:?POLY_BYTES/binary>>, _, [_, _, _, _] = Parts) ->
    _ = polynomial(C1),
    Phase = lists:foldl(fun(Part, Acc) ->
        lists:zipwith(fun(A, B) -> (A + B) rem ?Q end, polynomial(Part), Acc)
    end, polynomial(C0), Parts),
    [Bit | Tail] = [((4 * A + ?Q) div (2 * ?Q)) rem 2 || A <- Phase],
    true = Tail =:= lists:duplicate(?N - 1, 0),
    Bit.

polynomial(Bytes) when byte_size(Bytes) =:= ?POLY_BYTES ->
    Coefficients = [A || <<A:128/big>> <= Bytes],
    true = lists:all(fun(A) -> A < ?Q end, Coefficients),
    Coefficients.
