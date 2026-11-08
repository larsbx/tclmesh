%% SQLite adapter for the inert Q45 actor, never a cryptographic verifier.
-module(q45_result_store).
-export([new/2, lookup/2, commit/4, binding/1]).

new(Database, Worker) ->
    #{database => filename:absname(Database), worker => filename:absname(Worker),
      python => os:find_executable("python3"), timeout_ms => 10000}.

%% The local binding includes exact bytes, their digest and canonical quorum.
%% The P1 designation is a deterministic function of this quorum. No network
%% agreement, key-setup transcript or cryptographic authenticity is implied.
binding({Ciphertext, Digest, Quorum})
  when is_binary(Ciphertext), byte_size(Ciphertext) > 0,
       byte_size(Ciphertext) =< 262144, is_binary(Digest), byte_size(Digest) =:= 32,
       is_list(Quorum), length(Quorum) =:= 4 ->
    case crypto:hash(sha256, Ciphertext) =:= Digest andalso
         lists:usort(Quorum) =:= Quorum andalso
         lists:all(fun(I) -> is_integer(I) andalso I >= 1 andalso I =< 5 end, Quorum) of
        true -> {ok, term_to_binary({q45_local_binding_v1, Ciphertext, Digest, Quorum},
                                   [deterministic])};
        false -> {error, invalid_result_binding}
    end;
binding(_) -> {error, invalid_result_binding}.

lookup(Store, Sid) when is_binary(Sid), byte_size(Sid) > 0, byte_size(Sid) =< 512 ->
    case request(Store, [<<"lookup">>, binary:encode_hex(Sid)]) of
        {ok, <<"empty">>} -> empty;
        {ok, Response} -> decode(Response, Sid, lookup);
        _ -> {error, persistence_failed}
    end;
lookup(_, _) -> {error, invalid_session}.

commit(Store, Sid, Binding, Bit)
  when is_binary(Sid), byte_size(Sid) > 0, byte_size(Sid) =< 512,
       is_binary(Binding), byte_size(Binding) > 0, byte_size(Binding) =< 524288,
       (Bit =:= 0 orelse Bit =:= 1) ->
    case request(Store, [<<"commit">>, binary:encode_hex(Sid),
                         binary:encode_hex(Binding), integer_to_binary(Bit)]) of
        {ok, <<"conflict">>} -> {error, result_conflict};
        {ok, Response} ->
            case decode(Response, Sid, commit) of
                {Status, #{binding := Binding, result := Bit}} = Result
                  when Status =:= inserted; Status =:= replay -> Result;
                _ -> {error, persistence_failed}
            end;
        _ -> {error, persistence_failed}
    end;
commit(_, _, _, _) -> {error, invalid_result}.

decode(Response, Sid, Operation) ->
    try
        case binary:split(Response, <<"\t">>, [global]) of
            [Status, HexBinding, BitBytes, HexId] ->
                Binding = binary:decode_hex(HexBinding),
                Bit = binary_to_integer(BitBytes),
                Id = binary:decode_hex(HexId),
                true = byte_size(Binding) > 0 andalso byte_size(Binding) =< 524288,
                true = BitBytes =:= <<"0">> orelse BitBytes =:= <<"1">>,
                Id = crypto:hash(sha256, <<"tclmesh-q45-result-v1", 0,
                    (byte_size(Sid)):64/unsigned-big, Sid/binary,
                    (byte_size(Binding)):64/unsigned-big, Binding/binary, Bit:8>>),
                Receipt = #{id => Id, binding => Binding, result => Bit},
                case {Operation, Status} of
                    {lookup, <<"found">>} -> {ok, Receipt};
                    {commit, <<"inserted">>} -> {inserted, Receipt};
                    {commit, <<"replay">>} -> {replay, Receipt};
                    _ -> {error, persistence_failed}
                end;
            _ -> {error, persistence_failed}
        end
    catch _:_ -> {error, persistence_failed}
    end.

request(#{database := Database, worker := Worker, python := Python,
          timeout_ms := Timeout}, Fields) when is_list(Python) ->
    try
        Port = open_port({spawn_executable, Python},
            [binary, exit_status, use_stdio, stderr_to_stdout,
             {args, ["-B", Worker, "--db", Database]}]),
        true = port_command(Port, [lists:join(<<"\t">>, Fields), <<"\n">>]),
        Deadline = erlang:monotonic_time(millisecond) + Timeout,
        collect(Port, <<>>, Deadline)
    catch _:_ -> {error, persistence_failed}
    end;
request(_, _) -> {error, persistence_failed}.

collect(Port, Output, Deadline) ->
    Remaining = max(0, Deadline - erlang:monotonic_time(millisecond)),
    receive
        {Port, {data, Bytes}} when byte_size(Output) + byte_size(Bytes) =< 2097152 ->
            collect(Port, <<Output/binary, Bytes/binary>>, Deadline);
        {Port, {data, _}} ->
            catch port_close(Port),
            {error, persistence_failed};
        {Port, {exit_status, 0}} ->
            case binary:split(Output, <<"\n">>, [global]) of
                [Line, <<>>] -> {ok, Line};
                _ -> {error, persistence_failed}
            end;
        {Port, {exit_status, _}} -> {error, persistence_failed}
    after Remaining ->
        catch port_close(Port),
        {error, persistence_failed}
    end.
