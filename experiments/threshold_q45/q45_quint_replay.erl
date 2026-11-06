%% Test-only projection check for a generated Quint trace with real P2b bytes.
%% No release API. The arithmetic decoder is independent of the Python oracle.
-module(q45_quint_replay).
-export([run/1]).
-define(Q, ((1 bsl 127) - 1)).
-define(N, 32).
-define(BYTES, (?N * 16)).

run(Path) ->
    {ok, [{fixture, Inputs, Ciphertext, Quorum, Initial} | Rows]} = file:consult(Path),
    Sid = <<"quint-p2b-conformance">>,
    Digest = crypto:hash(sha256, Ciphertext),
    Binding = {Ciphertext, Digest, Quorum},
    Evaluate = fun(Ordered) when Ordered =:= Inputs -> Ciphertext end,
    {ok, Pid} = q45_ceremony:start_link(Sid, 10000, Evaluate, fun combine/3),
    try
        check(Initial, sys:get_state(Pid)),
        lists:foreach(fun({Abstract, Expected}) ->
            Event = event(Abstract, Inputs, Digest, Binding),
            ok = q45_ceremony:submit(Pid, Sid, Event),
            check(Expected, sys:get_state(Pid))
        end, Rows),
        io:format("Quint/P2b/P1 projection: ~B snapshots match~n", [length(Rows) + 1])
    after
        gen_statem:stop(Pid)
    end.

event({input, I}, Inputs, _, _) -> {input, I, lists:nth(I, Inputs)};
event({seal, I}, _, Digest, _) -> {seal, I, Digest};
event({commit, I}, _, Digest, _) -> {commit, I, Digest};
event({partial, I, Part}, _, _, Binding) -> {partial, I, Binding, Part};
event({result, Bit}, _, _, Binding) -> {result, Binding, Bit}.

check(Expected, {Phase, Data}) ->
    Keys = fun(Key) -> lists:sort(maps:keys(maps:get(Key, Data, #{}))) end,
    Actual = {Phase, Keys(inputs), Keys(seals), Keys(commits),
              maps:get(quorum, Data, []), Keys(partials), maps:get(result, Data, -1)},
    case Actual =:= Expected of
        true -> ok;
        false -> error({projection_mismatch, Expected, Actual})
    end.

combine(<<C0:?BYTES/binary, C1:?BYTES/binary>>, _, [_, _, _, _] = Parts) ->
    _ = polynomial(C1),
    Phase = lists:foldl(fun(Part, Acc) ->
        lists:zipwith(fun(A, B) -> (A + B) rem ?Q end, polynomial(Part), Acc)
    end, polynomial(C0), Parts),
    [Bit | Tail] = [((4 * A + ?Q) div (2 * ?Q)) rem 2 || A <- Phase],
    true = Tail =:= lists:duplicate(?N - 1, 0),
    Bit.

polynomial(Bytes) when byte_size(Bytes) =:= ?BYTES ->
    Coefficients = [A || <<A:128/big>> <= Bytes],
    true = lists:all(fun(A) -> A < ?Q end, Coefficients),
    Coefficients.
