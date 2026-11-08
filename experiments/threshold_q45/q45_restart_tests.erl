%% Process-crash acceptance driver for the inert SPEC_4of5 actor. The Python
%% runner owns process SIGKILL, independent SQLite inspection, and evidence.
%% This exercises local persistence; it is not a threshold-release protocol.
-module(q45_restart_tests).

-export([run/4]).

-define(BUDGET_MS, 10000).
-define(WAIT_MS, 15000).

run(Mode, Database, Worker, Marker) ->
    process_flag(trap_exit, true),
    {ok, _} = application:ensure_all_started(crypto),
    Store = q45_result_store:new(Database, Worker),
    case Mode of
        actor_after_commit -> actor_crash(Store, after_commit, 0);
        actor_after_completion -> actor_crash(Store, after_completion, 1);
        vm_after_commit -> vm_crash(Store, after_commit, 0, Marker);
        vm_after_completion -> vm_crash(Store, after_completion, 1, Marker);
        replay -> replay(Store);
        stale_writer -> stale_writer(Store);
        identical_race -> identical_race(Store);
        unavailable_store -> unavailable_store(Store, Database);
        lost_helper_response -> lost_helper_response(Store);
        normal_retry -> normal_retry(Store);
        _ -> erlang:error({unknown_restart_check, Mode})
    end,
    io:format("Q45_CHECK_OK ~p~n", [Mode]),
    ok.

sid() -> <<"q45-invq9-restart">>.
ciphertext() -> <<"evaluated:", 1, 2, 3, 4, 5>>.
quorum() -> [1, 2, 3, 4].
digest() -> crypto:hash(sha256, ciphertext()).
binding() -> {ciphertext(), digest(), quorum()}.
share(I) -> <<I, "toy share">>.

evaluate(Inputs) -> iolist_to_binary([<<"evaluated:">> | Inputs]).

combine(Bit) ->
    fun(Ciphertext, Quorum, Shares) ->
        expect(ciphertext(), Ciphertext, combiner_ciphertext),
        expect(quorum(), Quorum, combiner_quorum),
        expect([share(I) || I <- quorum()], Shares, combiner_shares),
        Bit
    end.

start_actor(Store, Hooks, Budget, Combine) ->
    {ok, Pid} = q45_ceremony:start_link(
        sid(), Budget, fun evaluate/1, Combine,
        #{result_store => Store, completion_sink => self(), hooks => Hooks}),
    unlink(Pid),
    Pid.

start_actor(Store) -> start_actor(Store, #{}, ?BUDGET_MS, combine(1)).

prepare(Pid) ->
    Events = [{input, I, <<I>>} || I <- lists:seq(1, 5)] ++
             [{seal, I, digest()} || I <- lists:seq(1, 5)] ++
             [{commit, I, digest()} || I <- quorum()] ++
             [{partial, I, binding(), share(I)} || I <- quorum()],
    lists:foreach(
        fun(Event) -> expect(ok, q45_ceremony:submit(Pid, sid(), Event), Event) end,
        Events),
    {result, _} = sys:get_state(Pid),
    ok.

result(Pid, Bit) -> q45_ceremony:submit(Pid, sid(), {result, binding(), Bit}).

expected_receipt() ->
    Sid = sid(),
    {ok, Binding} = q45_result_store:binding(binding()),
    Id = crypto:hash(sha256,
        <<"tclmesh-q45-result-v1", 0,
          (byte_size(Sid)):64/unsigned-big, Sid/binary,
          (byte_size(Binding)):64/unsigned-big, Binding/binary, 1:8>>),
    #{id => Id, binding => Binding, result => 1}.

assert_receipt(Receipt) -> expect(expected_receipt(), Receipt, durable_receipt).

%% The sys call is a mailbox barrier: a notification sent by the same actor
%% before its system reply must already be in this observer's mailbox.
barrier(Pid) ->
    {complete, #{result := 1, durable_receipt := Receipt}} = sys:get_state(Pid),
    assert_receipt(Receipt),
    ok.

assert_replays(Pid, Receipt) ->
    expect({ok, Receipt}, result(Pid, 1), identical_retry),
    expect({ok, Receipt}, result(Pid, 1), repeated_identical_retry),
    expect({error, result_conflict}, result(Pid, 0), conflicting_bit),
    OtherCiphertext = <<"different evaluated transcript">>,
    OtherBinding = {OtherCiphertext, crypto:hash(sha256, OtherCiphertext), quorum()},
    expect({error, result_conflict},
        q45_ceremony:submit(Pid, sid(), {result, OtherBinding, 1}),
        conflicting_transcript),
    OtherQuorum = {ciphertext(), digest(), [1, 2, 3, 5]},
    expect({error, result_conflict},
        q45_ceremony:submit(Pid, sid(), {result, OtherQuorum, 1}),
        conflicting_quorum),
    expect({error, result_conflict},
        q45_ceremony:submit(Pid, sid(), {result, {ciphertext(), <<0:256>>, quorum()}, 1}),
        invalid_binding),
    barrier(Pid).

notifications() -> notifications([]).
notifications(Acc) ->
    receive
        {q45_complete, Sid, Receipt} -> notifications([{Sid, Receipt} | Acc])
    after 0 -> lists:reverse(Acc)
    end.

expect_notifications(Expected, Receipt) ->
    Events = notifications(),
    lists:foreach(fun({Sid, Actual}) ->
        expect(sid(), Sid, completion_session),
        expect(Receipt, Actual, completion_receipt)
    end, Events),
    Count = length(Events),
    case Count of
        Expected -> ok;
        _ when Count > Expected -> erlang:error({duplicate_completion, Count});
        _ -> erlang:error({missing_completion, expected, Expected, actual, Count})
    end.

normal_retry(Store) ->
    Pid = start_actor(Store),
    prepare(Pid),
    {ok, Receipt} = result(Pid, 1),
    assert_receipt(Receipt),
    barrier(Pid),
    expect_notifications(1, Receipt),
    assert_replays(Pid, Receipt),
    expect_notifications(0, Receipt),
    ok = gen_statem:stop(Pid).

replay(Store) ->
    {ok, Receipt} = q45_result_store:lookup(Store, sid()),
    assert_receipt(Receipt),
    Pid = start_actor(Store),
    barrier(Pid),
    assert_replays(Pid, Receipt),
    expect_notifications(0, Receipt),
    expect({ok, Receipt}, q45_result_store:lookup(Store, sid()), replay_store),
    ok = gen_statem:stop(Pid).

blocking_hook(Observer, Stage) ->
    fun(Receipt) ->
        Observer ! {at_hook, self(), Stage, Receipt},
        receive
            never_resume_crash_hook -> erlang:error(crash_hook_was_resumed)
        end
    end.

async_result(Pid, Bit) ->
    Observer = self(),
    Ref = make_ref(),
    spawn(fun() ->
        Reply = catch result(Pid, Bit),
        Observer ! {result_reply, Ref, Reply}
    end),
    Ref.

await_hook(Pid, Stage) ->
    receive
        {at_hook, Pid, Stage, Receipt} ->
            assert_receipt(Receipt),
            Receipt
    after ?WAIT_MS -> erlang:error({hook_not_reached, Stage})
    end.

await_reply(Ref) ->
    receive
        {result_reply, Ref, Reply} -> Reply
    after ?WAIT_MS -> erlang:error(result_reply_timeout)
    end.

actor_crash(Store, Stage, NotificationCount) ->
    Pid = start_actor(Store, #{Stage => blocking_hook(self(), Stage)},
                      ?BUDGET_MS, combine(1)),
    prepare(Pid),
    Ref = async_result(Pid, 1),
    Receipt = await_hook(Pid, Stage),
    %% The hook message follows notification from this same actor, so receiving
    %% it also acknowledges every notification preceding this crash window.
    expect_notifications(NotificationCount, Receipt),
    expect({ok, Receipt}, q45_result_store:lookup(Store, sid()), committed_before_kill),
    Monitor = erlang:monitor(process, Pid),
    exit(Pid, kill),
    receive
        {'DOWN', Monitor, process, Pid, killed} -> ok
    after ?WAIT_MS -> erlang:error(actor_not_killed)
    end,
    case await_reply(Ref) of
        {'EXIT', _} -> ok;
        Other -> erlang:error({acknowledged_before_crash, Other})
    end,
    Recovered = start_actor(Store),
    assert_replays(Recovered, Receipt),
    expect_notifications(0, Receipt),
    expect({ok, Receipt}, q45_result_store:lookup(Store, sid()), retained_after_restart),
    ok = gen_statem:stop(Recovered).

vm_crash(Store, Stage, NotificationCount, Marker) ->
    Pid = start_actor(Store, #{Stage => blocking_hook(self(), Stage)},
                      ?BUDGET_MS, combine(1)),
    prepare(Pid),
    _ = async_result(Pid, 1),
    Receipt = await_hook(Pid, Stage),
    expect_notifications(NotificationCount, Receipt),
    expect({ok, Receipt}, q45_result_store:lookup(Store, sid()), committed_before_vm_kill),
    %% fsync the observation only after the parent has consumed all expected
    %% notifications. The external runner now kills the entire blocked VM.
    Json = io_lib:format("{\"stage\":\"~s\",\"notifications\":~B}\n",
                         [atom_to_list(Stage), NotificationCount]),
    TemporaryMarker = Marker ++ ".tmp",
    {ok, File} = file:open(TemporaryMarker, [write, binary, raw]),
    ok = file:write(File, Json),
    ok = file:sync(File),
    ok = file:close(File),
    ok = file:rename(TemporaryMarker, Marker),
    receive
        never_resume_vm_crash -> erlang:error(vm_crash_was_resumed)
    end.

stale_writer(Store) ->
    Winner = start_actor(Store),
    Stale = start_actor(Store, #{}, ?BUDGET_MS, combine(0)),
    prepare(Winner),
    prepare(Stale),
    {ok, Receipt} = result(Winner, 1),
    assert_receipt(Receipt),
    barrier(Winner),
    expect_notifications(1, Receipt),
    expect({error, result_conflict}, result(Stale, 0), stale_conflicting_writer),
    assert_replays(Stale, Receipt),
    expect_notifications(0, Receipt),
    expect({ok, Receipt}, q45_result_store:lookup(Store, sid()), stale_store),
    ok = gen_statem:stop(Winner),
    ok = gen_statem:stop(Stale).

identical_race(Store) ->
    Observer = self(),
    Token = make_ref(),
    Inner = combine(1),
    Combine = fun(Ciphertext, Quorum, Shares) ->
        %% actor_step already read an empty store before reaching Combine.
        %% Both actors must arrive here before either is allowed to commit.
        Observer ! {combiner_ready, Token, self()},
        receive {combine_go, Token} -> Inner(Ciphertext, Quorum, Shares)
        after ?WAIT_MS -> erlang:error(combiner_barrier_timeout)
        end
    end,
    First = start_actor(Store, #{}, ?BUDGET_MS, Combine),
    Second = start_actor(Store, #{}, ?BUDGET_MS, Combine),
    prepare(First),
    prepare(Second),
    FirstRef = async_result(First, 1),
    SecondRef = async_result(Second, 1),
    await_combiner(First, Token),
    await_combiner(Second, Token),
    First ! {combine_go, Token},
    Second ! {combine_go, Token},
    {ok, Receipt} = await_reply(FirstRef),
    assert_receipt(Receipt),
    expect({ok, Receipt}, await_reply(SecondRef), identical_race_receipt),
    barrier(First),
    barrier(Second),
    %% Required semantic mutation oracle: injecting notify_completion into the
    %% store's replay branch yields two messages and must fail with this tag.
    expect_notifications(1, Receipt),
    assert_replays(First, Receipt),
    assert_replays(Second, Receipt),
    expect_notifications(0, Receipt),
    expect({ok, Receipt}, q45_result_store:lookup(Store, sid()), race_store),
    ok = gen_statem:stop(First),
    ok = gen_statem:stop(Second).

await_combiner(Pid, Token) ->
    receive {combiner_ready, Token, Pid} -> ok
    after ?WAIT_MS -> erlang:error({combiner_not_reached, Pid})
    end.

unavailable_store(Store, Database) ->
    Pid = start_actor(Store),
    prepare(Pid),
    Backup = Database ++ ".held",
    ok = file:rename(Database, Backup),
    ok = file:make_dir(Database),
    try
        expect({error, persistence_failed}, result(Pid, 1), unavailable_commit),
        {result, _} = sys:get_state(Pid),
        expect_notifications(0, expected_receipt()),
        expect({error, {result_store_unavailable, persistence_failed}},
            q45_ceremony:start_link(sid(), ?BUDGET_MS, fun evaluate/1, combine(1),
                                   #{result_store => Store, completion_sink => self()}),
            unavailable_start)
    after
        ok = file:del_dir(Database),
        ok = file:rename(Backup, Database),
        ok = gen_statem:stop(Pid)
    end,
    expect(empty, q45_result_store:lookup(Store, sid()), no_result_when_unavailable),
    expect_notifications(0, expected_receipt()).

lost_helper_response(Store) ->
    %% The runner supplies a wrapper that commits successfully, then discards
    %% the commit response. Its lookup path still delegates to the real worker.
    Pid = start_actor(Store, #{}, 1000, combine(1)),
    prepare(Pid),
    expect({error, persistence_failed}, result(Pid, 1), lost_commit_response),
    {ok, Receipt} = q45_result_store:lookup(Store, sid()),
    assert_receipt(Receipt),
    expect_notifications(0, Receipt),
    wait_aborted(Pid, erlang:monotonic_time(millisecond) + ?WAIT_MS),
    {aborted, #{deadline := Deadline}} = sys:get_state(Pid),
    expect(true, erlang:monotonic_time(millisecond) >= Deadline, deadline_elapsed),
    %% Recovery must consult durable authority before testing fresh eligibility.
    assert_replays(Pid, Receipt),
    expect_notifications(0, Receipt),
    expect({ok, Receipt}, q45_result_store:lookup(Store, sid()), recovered_lost_response),
    ok = gen_statem:stop(Pid).

wait_aborted(Pid, Limit) ->
    case sys:get_state(Pid) of
        {aborted, _} -> ok;
        {result, _} ->
            case erlang:monotonic_time(millisecond) < Limit of
                true -> timer:sleep(10), wait_aborted(Pid, Limit);
                false -> erlang:error(deadline_did_not_expire)
            end;
        Other -> erlang:error({unexpected_lost_response_state, Other})
    end.

expect(Expected, Actual, _Label) when Expected =:= Actual -> ok;
expect(Expected, Actual, Label) ->
    erlang:error({assertion_failed, Label, expected, Expected, actual, Actual}).
