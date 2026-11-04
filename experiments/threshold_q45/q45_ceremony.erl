%% Inert SPEC_4of5 research model. Callers supply simulated evaluation and
%% combination. Party numbers and opaque payloads are test data; this module
%% performs no authentication, share generation, verification, or release.
-module(q45_ceremony).
-behaviour(gen_statem).

-export([start_link/4, submit/3, new/5, step/3]).
-export([init/1, callback_mode/0, handle_event/4]).

-define(PARTIES, [1, 2, 3, 4, 5]).

start_link(Sid, BudgetMs, Evaluate, Combine) ->
    gen_statem:start_link(?MODULE, {Sid, BudgetMs, Evaluate, Combine}, []).

submit(Pid, Sid, Event) ->
    gen_statem:call(Pid, {Sid, Event}, infinity).

init({Sid, BudgetMs, Evaluate, Combine}) ->
    {Phase, Data} = new(Sid, BudgetMs, Evaluate, Combine, now_ms()),
    {ok, Phase, Data, timer_action(Phase, Data)}.

callback_mode() -> handle_event_function.

handle_event({call, From}, {Sid, Event}, Phase, Data) ->
    {Reply, {Next, Updated}} = step({Phase, Data}, {Sid, Event}, now_ms()),
    Actions = [{reply, From, Reply}],
    case Next =:= Phase of
        true -> {keep_state, Updated, Actions};
        false -> {next_state, Next, Updated, Actions ++ timer_action(Next, Updated)}
    end;
handle_event(state_timeout, expire, Phase, Data) ->
    {_, {Next, Updated}} = step({Phase, Data}, expire, now_ms()),
    {next_state, Next, Updated, timer_action(Next, Updated)};
handle_event({call, From}, _, _, _) ->
    {keep_state_and_data, [{reply, From, {error, invalid_event}}]};
handle_event(_, _, _, _) ->
    keep_state_and_data.

now_ms() -> erlang:monotonic_time(millisecond).

timer_action(Phase, _) when Phase =:= complete; Phase =:= aborted -> [];
timer_action(_, #{deadline := Deadline}) ->
    [{state_timeout, max(0, Deadline - now_ms()), expire}].

%% step/3 takes trusted, nondecreasing logical time for deterministic replay.
%% start_link/4 supplies a local monotonic clock; submitted events carry no time.
new(Sid, Budget, Evaluate, Combine, Now)
  when is_binary(Sid), byte_size(Sid) > 0, is_integer(Budget), Budget > 0,
       is_function(Evaluate, 1), is_function(Combine, 3), is_integer(Now) ->
    {inputs, #{sid => Sid, budget => Budget, deadline => Now + Budget,
               evaluate => Evaluate, combine => Combine, inputs => #{}}}.

step({Phase, _} = State, _, _) when Phase =:= aborted; Phase =:= complete ->
    reject(terminal, State);
step({_, #{deadline := Deadline} = Data}, _, Now) when Now >= Deadline ->
    {{error, timeout}, {aborted, Data}};
step({Phase, #{sid := Sid} = Data}, {Sid, Event}, Now) ->
    transition(Phase, Data, Event, Now);
step(State, _, _) ->
    reject(unbound_or_early_timeout, State).

transition(inputs, #{inputs := Inputs} = Data, {input, I, Ciphertext}, Now)
  when is_integer(I), I >= 1, I =< 5, is_binary(Ciphertext), byte_size(Ciphertext) > 0,
       not is_map_key(I, Inputs) ->
    Updated = Inputs#{I => Ciphertext},
    case map_size(Updated) of
        5 -> start_sealing(Data#{inputs := Updated}, Now);
        _ -> {ok, {inputs, Data#{inputs := Updated}}}
    end;
transition(sealing, #{seals := Seals, digest := ExpectedDigest} = Data,
           {seal, I, Digest}, Now)
  when is_integer(I), I >= 1, I =< 5, Digest =:= ExpectedDigest,
       not is_map_key(I, Seals) ->
    Updated = Seals#{I => true},
    case map_size(Updated) of
        5 -> advance(quorum, Data#{seals := Updated, commits => #{}}, Now);
        _ -> {ok, {sealing, Data#{seals := Updated}}}
    end;
transition(quorum, #{commits := Commits, digest := ExpectedDigest} = Data,
           {commit, I, Digest}, Now)
  when is_integer(I), I >= 1, I =< 5, Digest =:= ExpectedDigest,
       not is_map_key(I, Commits) ->
    Updated = Commits#{I => true},
    case map_size(Updated) of
        4 ->
            S = lists:sort(maps:keys(Updated)),
            advance(partials, Data#{commits := Updated, quorum => S,
                                    designation => designation(S), partials => #{}}, Now);
        _ -> {ok, {quorum, Data#{commits := Updated}}}
    end;
transition(partials, #{ciphertext := ExpectedCiphertext, digest := Digest,
                       quorum := S, partials := Parts} = Data,
           {partial, I, {Ciphertext, Digest, S}, Share}, Now)
  when Ciphertext =:= ExpectedCiphertext, is_binary(Share), byte_size(Share) > 0,
       not is_map_key(I, Parts) ->
    case lists:member(I, S) of
        true ->
            Updated = Parts#{I => Share},
            case map_size(Updated) of
                4 -> advance(result, Data#{partials := Updated}, Now);
                _ -> {ok, {partials, Data#{partials := Updated}}}
            end;
        false -> reject(outside_quorum, {partials, Data})
    end;
transition(result, #{ciphertext := Ciphertext, digest := Digest, quorum := S,
                     partials := Parts, combine := Combine} = Data,
           {result, {Ciphertext, Digest, S}, Bit}, _)
  when Bit =:= 0; Bit =:= 1 ->
    try Combine(Ciphertext, S, [maps:get(I, Parts) || I <- S]) of
        Bit -> {ok, {complete, Data#{result => Bit}}};
        Other when Other =:= 0; Other =:= 1 -> reject(inconsistent_result, {result, Data});
        _ -> {{error, combiner_failed}, {aborted, Data}}
    catch
        _:_ -> {{error, combiner_failed}, {aborted, Data}}
    end;
transition(Phase, Data, _, _) ->
    reject(invalid_event, {Phase, Data}).

start_sealing(#{inputs := Inputs, evaluate := Evaluate} = Data, Now) ->
    try Evaluate([maps:get(I, Inputs) || I <- ?PARTIES]) of
        Ciphertext when is_binary(Ciphertext), byte_size(Ciphertext) > 0 ->
            Digest = crypto:hash(sha256, Ciphertext),
            advance(sealing, Data#{ciphertext => Ciphertext, digest => Digest, seals => #{}}, Now);
        _ -> {{error, evaluator_failed}, {aborted, Data}}
    catch
        _:_ -> {{error, evaluator_failed}, {aborted, Data}}
    end.

advance(Phase, #{budget := Budget} = Data, Now) ->
    {ok, {Phase, Data#{deadline := Now + Budget}}}.

designation(S) ->
    [{[A, B, C], hd(S -- [A, B, C])}
     || A <- ?PARTIES, B <- ?PARTIES, C <- ?PARTIES, A < B, B < C].

reject(Reason, State) -> {{error, Reason}, State}.
