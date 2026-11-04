-module(q45_ceremony_tests).
-include_lib("eunit/include/eunit.hrl").

-define(SID, <<"q45-session">>).
-define(PARTIES, [1, 2, 3, 4, 5]).
-define(TIMEOUT, 10).

input(I) -> {input, I, <<I>>}.
share(I) -> <<I, "toy share">>.
evaluate(Inputs) -> iolist_to_binary([<<"evaluated:">> | Inputs]).
ciphertext() -> <<"evaluated:", 1, 2, 3, 4, 5>>.
digest() -> crypto:hash(sha256, ciphertext()).
combine(Ciphertext, Quorum, Shares) ->
    Ciphertext = ciphertext(),
    Shares = [share(I) || I <- Quorum],
    1.

new() ->
    q45_ceremony:new(?SID, ?TIMEOUT, fun evaluate/1, fun combine/3, 0).

seal(I) -> {seal, I, digest()}.
commit(I) -> {commit, I, digest()}.
binding(S) -> {ciphertext(), digest(), S}.
partial(I, S) -> {partial, I, binding(S), share(I)}.
result(S, Bit) -> {result, binding(S), Bit}.

step(State, Event, Time) ->
    q45_ceremony:step(State, {?SID, Event}, Time).

accept(State, Event) ->
    {ok, Next} = step(State, Event, 0),
    Next.

apply_all(State, Events) -> lists:foldl(fun(E, D) -> accept(D, E) end, State, Events).

reject(State, Event) ->
    ?assertMatch({{error, _}, State}, step(State, Event, 0)).

inputs() -> [input(I) || I <- ?PARTIES].
seals() -> [seal(I) || I <- ?PARTIES].
quorum() -> [1, 2, 3, 4].
commits() -> [commit(I) || I <- quorum()].
partials() -> [partial(I, quorum()) || I <- quorum()].
prefix() -> inputs() ++ seals() ++ commits().

all_five_inputs_and_matching_attestations_test() ->
    Four = apply_all(new(), lists:sublist(inputs(), 4)),
    reject(Four, input(4)),
    reject(Four, {input, 6, <<6>>}),
    reject(Four, seal(1)),
    reject(Four, commit(1)),
    reject(Four, partial(1, quorum())),
    All = accept(Four, input(5)),
    reject(All, {seal, 1, <<0:256>>}),
    FourSeals = apply_all(All, lists:sublist(seals(), 4)),
    reject(FourSeals, seal(4)),
    reject(FourSeals, commit(1)),
    reject(accept(FourSeals, seal(5)), {commit, 1, <<0:256>>}).

freeze_before_any_partial_test() ->
    Three = apply_all(new(), inputs() ++ seals() ++ lists:sublist(commits(), 3)),
    reject(Three, commit(3)),
    reject(Three, partial(1, quorum())),
    Frozen = accept(Three, commit(4)),
    ?assertMatch({partials, #{quorum := [1, 2, 3, 4], designation := [_, _, _, _, _, _, _, _, _, _]}}, Frozen),
    reject(Frozen, commit(5)),
    reject(Frozen, partial(5, quorum())),
    reject(Frozen, partial(1, [1, 2, 3, 5])),
    reject(Frozen, partial(1, [4, 3, 2, 1])),
    One = accept(Frozen, partial(1, quorum())),
    reject(One, {partial, 1, binding(quorum()), <<"replacement">>}).

exact_ciphertext_test() ->
    Frozen = apply_all(new(), prefix()),
    Wrong = <<"foreign ciphertext">>,
    reject(Frozen, {partial, 1, {Wrong, digest(), quorum()}, share(1)}),
    reject(Frozen, {partial, 1, {ciphertext(), crypto:hash(sha256, Wrong), quorum()}, share(1)}),
    reject(Frozen, {partial, 1, {Wrong, crypto:hash(sha256, Wrong), quorum()}, share(1)}),
    reject(Frozen, {partial, 1, binding(quorum()), <<>>}),
    ?assertMatch({ok, _}, step(Frozen, partial(1, quorum()), 0)).

other_session_and_same_session_replay_test() ->
    New = new(),
    ?assertMatch({{error, _}, New},
                 q45_ceremony:step(New, {<<"previous session">>, input(1)}, 0)),
    Started = accept(New, input(1)),
    reject(Started, input(1)),
    Frozen = apply_all(new(), prefix()),
    ?assertMatch({{error, _}, Frozen},
                 q45_ceremony:step(Frozen, {<<"previous session">>, partial(1, quorum())}, 0)),
    One = accept(Frozen, partial(1, quorum())),
    reject(One, partial(1, quorum())).

result_once_test() ->
    Frozen = apply_all(new(), prefix()),
    reject(Frozen, result(quorum(), 1)),
    Three = apply_all(Frozen, lists:sublist(partials(), 3)),
    reject(Three, result(quorum(), 1)),
    Ready = accept(Three, partial(4, quorum())),
    reject(Ready, result(quorum(), 0)),
    reject(Ready, result([1, 2, 3, 5], 1)),
    Wrong = <<"foreign result">>,
    reject(Ready, {result, {Wrong, digest(), quorum()}, 1}),
    ?assertMatch({{error, _}, Ready},
                 q45_ceremony:step(Ready, {<<"previous session">>, result(quorum(), 1)}, 0)),
    Complete = accept(Ready, result(quorum(), 1)),
    ?assertMatch({complete, #{result := 1}}, Complete),
    reject(Complete, result(quorum(), 1)),
    reject(Complete, result(quorum(), 0)),
    ?assertMatch({{error, _}, Complete}, q45_ceremony:step(Complete, expire, ?TIMEOUT)).

timeout_boundaries_test() ->
    Cases = [
        {lists:sublist(inputs(), 4), input(5)},
        {inputs() ++ lists:sublist(seals(), 4), seal(5)},
        {inputs() ++ seals() ++ lists:sublist(commits(), 3), commit(4)},
        {prefix(), partial(1, quorum())},
        {prefix() ++ lists:sublist(partials(), 3), partial(4, quorum())},
        {prefix() ++ partials(), result(quorum(), 1)}
    ],
    lists:foreach(fun({Prefix, Event}) ->
        State = apply_all(new(), Prefix),
        ?assertMatch({ok, _}, step(State, Event, ?TIMEOUT - 1)),
        ?assertMatch({{error, _}, State}, q45_ceremony:step(State, expire, ?TIMEOUT - 1)),
        {Reply, Aborted} = step(State, Event, ?TIMEOUT),
        ?assertMatch({{error, timeout}, {aborted, _}}, {Reply, Aborted}),
        ?assertMatch({{error, timeout}, Aborted}, q45_ceremony:step(State, expire, ?TIMEOUT)),
        ?assertMatch({{error, _}, Aborted}, step(Aborted, Event, ?TIMEOUT + 1)),
        ?assertMatch({{error, _}, Aborted}, step(Aborted, commit(5), ?TIMEOUT + 1))
    end, Cases),
    {ok, Sealing} = step(apply_all(new(), lists:sublist(inputs(), 4)), input(5), ?TIMEOUT - 1),
    ?assertMatch({ok, _}, step(Sealing, seal(1), ?TIMEOUT)),
    {ok, StillSealing} = step(Sealing, seal(1), 2 * ?TIMEOUT - 2),
    ?assertMatch({{error, timeout}, {aborted, _}},
                 step(StillSealing, seal(2), 2 * ?TIMEOUT - 1)).

callback_failure_test() ->
    FailedEval = q45_ceremony:new(?SID, ?TIMEOUT, fun(_) -> error(eval) end, fun combine/3, 0),
    ?assertMatch({{error, evaluator_failed}, {aborted, _}},
                 step(apply_all(FailedEval, lists:sublist(inputs(), 4)), input(5), 0)),
    FailedCombine = q45_ceremony:new(?SID, ?TIMEOUT, fun evaluate/1, fun(_, _, _) -> other end, 0),
    ?assertMatch({{error, combiner_failed}, {aborted, _}},
                 step(apply_all(FailedCombine, prefix() ++ partials()), result(quorum(), 1), 0)).

actor_test() ->
    {ok, Pid} = q45_ceremony:start_link(?SID, 2000, fun evaluate/1, fun combine/3),
    try
        lists:foreach(fun(Event) -> ok = q45_ceremony:submit(Pid, ?SID, Event) end,
                      prefix() ++ partials() ++ [result(quorum(), 1)]),
        ?assertMatch({error, _}, q45_ceremony:submit(Pid, ?SID, result(quorum(), 1)))
    after
        gen_statem:stop(Pid)
    end,
    {ok, Idle} = q45_ceremony:start_link(?SID, 1, fun evaluate/1, fun combine/3),
    try
        % Wait for an idle timeout without issuing any protocol event.
        ?assertEqual(ok, await_abort(Idle, 100))
    after
        gen_statem:stop(Idle)
    end.

permutations([]) -> [[]];
permutations(List) -> [[I | Rest] || I <- List, Rest <- permutations(List -- [I])].

% Independent prefix language: each batch admits its remaining members. The
% commit batch admits any four of five, in arrival order. Binding and expected
% party membership come from the scenario, never from the state under test.
model_prefixes_test() ->
    lists:foreach(fun model_order/1, permutations(?PARTIES)).

model_order(Order) ->
    Selected = lists:sublist(Order, 4),
    S = lists:sort(Selected),
    InputBatch = [input(I) || I <- lists:reverse(Order)],
    SealBatch = [seal(I) || I <- tl(Order) ++ [hd(Order)]],
    CommitBatch = [commit(I) || I <- Order],
    PartialBatch = [partial(I, S) || I <- lists:reverse(Selected)],
    Result = result(S, 1),
    Universe = lists:usort(InputBatch ++ SealBatch ++ CommitBatch ++ PartialBatch ++
        [partial(I, S) || I <- ?PARTIES] ++
        [partial(I, lists:sort(?PARTIES -- [Other])) || I <- ?PARTIES, Other <- S] ++
        [{partial, I, {<<"other">>, digest(), S}, share(I)} || I <- ?PARTIES] ++
        [Result, result(S, 0)]),
    D1 = model_batch(new(), InputBatch, 5, Universe),
    D2 = model_batch(D1, SealBatch, 5, Universe),
    D3 = model_batch(D2, CommitBatch, 4, Universe),
    % Independent designation relation, enumerating holder pairs instead of
    % deriving their complements from the reducer's triple enumeration.
    Expected = lists:sort([{?PARTIES -- [A, B], hd([I || I <- [A, B], lists:member(I, S)])}
                          || A <- ?PARTIES, B <- ?PARTIES, A < B]),
    ?assertMatch({partials, #{quorum := S, designation := Expected}}, D3),
    D4 = model_batch(D3, PartialBatch, 4, Universe),
    Complete = model_batch(D4, [Result], 1, Universe),
    lists:foreach(fun(Event) -> reject(Complete, Event) end, Universe).

model_batch(State, _, 0, _) -> State;
model_batch(State, [Next | Rest] = Allowed, Count, Universe) ->
    lists:foreach(fun(Event) ->
        case lists:member(Event, Allowed) of
            true -> ?assertMatch({ok, _}, step(State, Event, 0));
            false -> reject(State, Event)
        end
    end, Universe),
    model_batch(accept(State, Next), Rest, Count - 1, Universe).

await_abort(_, 0) -> error(idle_timeout_did_not_fire);
await_abort(Pid, Attempts) ->
    case sys:get_state(Pid, 1000) of
        {aborted, _} -> ok;
        _ -> timer:sleep(5), await_abort(Pid, Attempts - 1)
    end.
