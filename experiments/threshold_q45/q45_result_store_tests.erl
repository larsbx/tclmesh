%% Acceptance tests for the local durable-result adapter, not cryptography.
-module(q45_result_store_tests).
-include_lib("eunit/include/eunit.hrl").

-define(SID, <<"q45-store-session">>).
-define(BINDING, <<"local transcript binding">>).

with_directory(Fun) ->
    Directory = filename:join("/tmp", "q45-store-tests-" ++ os:getpid() ++ "-" ++
                             integer_to_list(erlang:unique_integer([positive]))),
    ok = file:make_dir(Directory),
    try Fun(Directory)
    after file:del_dir_r(Directory)
    end.

store(Directory) ->
    Source = proplists:get_value(source, ?MODULE:module_info(compile)),
    Worker = filename:join([filename:dirname(Source), "..", "..",
                            "tools", "q45_result_store.py"]),
    q45_result_store:new(filename:join(Directory, "results.sqlite3"),
                         Worker).

receipt_id(Sid, Binding, Bit) ->
    crypto:hash(sha256, <<"tclmesh-q45-result-v1", 0,
        (byte_size(Sid)):64/unsigned-big, Sid/binary,
        (byte_size(Binding)):64/unsigned-big, Binding/binary, Bit:8>>).

wire(Status, Sid, Binding, Bit) ->
    Id = receipt_id(Sid, Binding, Bit),
    iolist_to_binary([Status, "\t", binary:encode_hex(Binding), "\t",
                      integer_to_binary(Bit), "\t", binary:encode_hex(Id), "\n"]).

fake_store(Directory, Response, ExitCode) ->
    Worker = filename:join(Directory, "fake.py"),
    ok = file:write_file(Worker, [
        "import sys\nsys.stdin.buffer.readline()\nsys.stdout.buffer.write(bytes.fromhex('",
        binary:encode_hex(Response), "'))\nsys.stdout.buffer.flush()\nsys.exit(",
        integer_to_list(ExitCode), ")\n"]),
    q45_result_store:new(filename:join(Directory, "unused.sqlite3"), Worker).

binding_is_deterministic_and_complete_test() ->
    Ciphertext = <<"evaluated ciphertext">>,
    Digest = crypto:hash(sha256, Ciphertext),
    Input = {Ciphertext, Digest, [1, 2, 3, 4]},
    {ok, Binding} = q45_result_store:binding(Input),
    ?assertEqual({ok, Binding}, q45_result_store:binding(Input)),
    ?assertEqual({q45_local_binding_v1, Ciphertext, Digest, [1, 2, 3, 4]},
                 binary_to_term(Binding, [safe])),
    {ok, OtherQuorum} = q45_result_store:binding({Ciphertext, Digest, [1, 2, 3, 5]}),
    ?assertNotEqual(Binding, OtherQuorum),
    OtherCiphertext = <<"other ciphertext">>,
    {ok, OtherBytes} = q45_result_store:binding(
        {OtherCiphertext, crypto:hash(sha256, OtherCiphertext), [1, 2, 3, 4]}),
    ?assertNotEqual(Binding, OtherBytes).

invalid_bindings_are_rejected_test() ->
    Ciphertext = <<"ciphertext">>,
    Digest = crypto:hash(sha256, Ciphertext),
    Invalid = [undefined, {<<>>, Digest, [1, 2, 3, 4]},
        {Ciphertext, <<0:256>>, [1, 2, 3, 4]},
        {Ciphertext, <<1>>, [1, 2, 3, 4]},
        {Ciphertext, Digest, [1, 2, 3]},
        {Ciphertext, Digest, [1, 2, 3, 4, 5]},
        {Ciphertext, Digest, [4, 3, 2, 1]},
        {Ciphertext, Digest, [1, 2, 3, 3]},
        {Ciphertext, Digest, [0, 1, 2, 3]},
        {Ciphertext, Digest, [1, 2, 3, 6]},
        {Ciphertext, Digest, [1, 2, 3, four]},
        {binary:copy(<<0>>, 262145), Digest, [1, 2, 3, 4]}],
    lists:foreach(fun(Value) ->
        ?assertEqual({error, invalid_result_binding}, q45_result_store:binding(Value))
    end, Invalid).

invalid_arguments_fail_before_io_test() ->
    lists:foreach(fun(Sid) ->
        ?assertEqual({error, invalid_session}, q45_result_store:lookup(#{}, Sid)),
        ?assertEqual({error, invalid_result},
                     q45_result_store:commit(#{}, Sid, ?BINDING, 1))
    end, [<<>>, not_binary, binary:copy(<<0>>, 513)]),
    lists:foreach(fun({Binding, Bit}) ->
        ?assertEqual({error, invalid_result},
                     q45_result_store:commit(#{}, ?SID, Binding, Bit))
    end, [{<<>>, 1}, {not_binary, 1}, {binary:copy(<<0>>, 524289), 1},
          {?BINDING, -1}, {?BINDING, 2}, {?BINDING, 1.0}, {?BINDING, true}]).

commit_replay_and_restart_return_same_receipt_test() ->
    with_directory(fun(Directory) ->
        Store = store(Directory),
        ?assertEqual(empty, q45_result_store:lookup(Store, ?SID)),
        {inserted, Receipt} = q45_result_store:commit(Store, ?SID, ?BINDING, 1),
        ?assertEqual(#{id => receipt_id(?SID, ?BINDING, 1),
                       binding => ?BINDING, result => 1}, Receipt),
        ?assertEqual({replay, Receipt}, q45_result_store:commit(Store, ?SID, ?BINDING, 1)),
        Reopened = store(Directory),
        ?assertEqual({ok, Receipt}, q45_result_store:lookup(Reopened, ?SID)),
        ?assertEqual({replay, Receipt},
                     q45_result_store:commit(Reopened, ?SID, ?BINDING, 1)),
        ?assertEqual(empty, q45_result_store:lookup(Reopened, <<"another session">>))
    end).

conflicting_retries_preserve_original_receipt_test() ->
    with_directory(fun(Directory) ->
        Store = store(Directory),
        {inserted, Receipt} = q45_result_store:commit(Store, ?SID, ?BINDING, 1),
        ?assertEqual({error, result_conflict},
                     q45_result_store:commit(Store, ?SID, ?BINDING, 0)),
        ?assertEqual({error, result_conflict},
                     q45_result_store:commit(Store, ?SID, <<"different binding">>, 1)),
        ?assertEqual({ok, Receipt}, q45_result_store:lookup(store(Directory), ?SID)),
        ?assertEqual({replay, Receipt}, q45_result_store:commit(Store, ?SID, ?BINDING, 1))
    end).

forged_receipt_hash_is_rejected_test() ->
    with_directory(fun(Directory) ->
        Forged = iolist_to_binary(["found\t", binary:encode_hex(?BINDING),
                                  "\t1\t", binary:encode_hex(<<0:256>>), "\n"]),
        Store = fake_store(Directory, Forged, 0),
        ?assertEqual({error, persistence_failed}, q45_result_store:lookup(Store, ?SID))
    end).

malformed_and_wrong_operation_responses_are_rejected_test() ->
    with_directory(fun(Directory) ->
        Valid = wire(<<"found">>, ?SID, ?BINDING, 1),
        Responses = [<<"empty\nextra\n">>, <<"empty">>, <<"error\n">>,
            wire(<<"inserted">>, ?SID, ?BINDING, 1),
            binary:replace(Valid, <<"\t1\t">>, <<"\t01\t">>),
            <<Valid/binary, "\n">>, <<"found\tzz\t1\t00\n">>],
        lists:foreach(fun(Response) ->
            Store = fake_store(Directory, Response, 0),
            ?assertEqual({error, persistence_failed}, q45_result_store:lookup(Store, ?SID))
        end, Responses),
        Found = fake_store(Directory, Valid, 0),
        ?assertEqual({error, persistence_failed},
                     q45_result_store:commit(Found, ?SID, ?BINDING, 1))
    end).

receipts_are_bound_to_request_fields_test() ->
    with_directory(fun(Directory) ->
        WrongSid = fake_store(Directory, wire(<<"found">>, <<"wrong sid">>, ?BINDING, 1), 0),
        ?assertEqual({error, persistence_failed}, q45_result_store:lookup(WrongSid, ?SID)),
        lists:foreach(fun(Response) ->
            Store = fake_store(Directory, Response, 0),
            ?assertEqual({error, persistence_failed},
                         q45_result_store:commit(Store, ?SID, ?BINDING, 1))
        end, [wire(<<"inserted">>, ?SID, <<"wrong binding">>, 1),
              wire(<<"replay">>, ?SID, ?BINDING, 0)])
    end).

worker_failures_and_timeouts_are_not_empty_test() ->
    with_directory(fun(Directory) ->
        Failed = fake_store(Directory, <<"empty\n">>, 1),
        ?assertEqual({error, persistence_failed}, q45_result_store:lookup(Failed, ?SID)),
        Missing = q45_result_store:new(filename:join(Directory, "unused.sqlite3"),
                                       filename:join(Directory, "missing.py")),
        ?assertEqual({error, persistence_failed}, q45_result_store:lookup(Missing, ?SID)),
        Worker = filename:join(Directory, "slow.py"),
        ok = file:write_file(Worker, "import sys,time\nsys.stdin.buffer.readline()\ntime.sleep(0.5)\n"),
        Slow = (q45_result_store:new(filename:join(Directory, "slow.sqlite3"), Worker))#{timeout_ms => 25},
        ?assertEqual({error, persistence_failed}, q45_result_store:lookup(Slow, ?SID)),
        ?assertEqual({error, persistence_failed}, q45_result_store:lookup(#{}, ?SID))
    end).
