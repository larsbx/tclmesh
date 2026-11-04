"""Run the same EUnit suite against the P1 ceremony and source-level mutants."""
import re
import subprocess
import tempfile
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[1] / "experiments" / "threshold_q45"

# (label, failing acceptance test, exact source fragment, replacement)
MUTANTS = [
    ("four inputs", "all_five_inputs_and_matching_attestations_test",
     "5 -> start_sealing(Data#{inputs := Updated}, Now);",
     "4 -> start_sealing(Data#{inputs := Updated#{5 => <<5>>}}, Now);"),
    ("inconsistent seal", "all_five_inputs_and_matching_attestations_test",
     "when is_integer(I), I >= 1, I =< 5, Digest =:= ExpectedDigest,\n"
     "       not is_map_key(I, Seals)",
     "when is_integer(I), I >= 1, I =< 5,\n"
     "       is_binary(Digest), is_binary(ExpectedDigest), not is_map_key(I, Seals)"),
    ("premature partial", "freeze_before_any_partial_test",
     "4 ->\n            S = lists:sort(maps:keys(Updated)),",
     "3 ->\n            Members = maps:keys(Updated),\n"
     "            S = lists:sort([hd(?PARTIES -- Members) | Members]),"),
    ("wrong ciphertext bytes", "exact_ciphertext_test",
     "when Ciphertext =:= ExpectedCiphertext, is_binary(Share), byte_size(Share) > 0,",
     "when is_binary(Ciphertext), is_binary(ExpectedCiphertext), is_binary(Share), byte_size(Share) > 0,"),
    ("wrong quorum binding", "freeze_before_any_partial_test",
     "{partial, I, {Ciphertext, Digest, S}, Share}, Now)",
     "{partial, I, {Ciphertext, Digest, _OtherQuorum}, Share}, Now)"),
    ("duplicate partial", "freeze_before_any_partial_test",
     "byte_size(Share) > 0,\n       not is_map_key(I, Parts) ->",
     "byte_size(Share) > 0 ->"),
    ("foreign session replay", "other_session_and_same_session_replay_test",
     "step({Phase, #{sid := Sid} = Data}, {Sid, Event}, Now) ->",
     "step({Phase, #{sid := _Sid} = Data}, {_ForeignSid, Event}, Now) ->"),
    ("repeat result", "result_once_test",
     "step({Phase, _} = State, _, _) when Phase =:= aborted; Phase =:= complete ->",
     "step({complete, _} = State, {_, {result, _, _}}, _) -> {ok, State};\n"
     "step({Phase, _} = State, _, _) when Phase =:= aborted; Phase =:= complete ->"),
    ("late acceptance at deadline", "timeout_boundaries_test",
     "when Now >= Deadline ->", "when Now > Deadline ->"),
]


def run_suite(source, directory):
    path = directory / "q45_ceremony.erl"
    path.write_text(source, encoding="utf-8")
    subprocess.run(
        ["erlc", "-Werror", "-o", directory, path, SOURCE / "q45_ceremony_tests.erl"],
        check=True, timeout=30,
    )
    return subprocess.run(
        ["erl", "-noshell", "-pa", directory, "-eval",
         "case eunit:test(q45_ceremony_tests, [verbose]) of ok -> halt(0); _ -> halt(1) end."],
        cwd=directory, capture_output=True, text=True, timeout=30,
    )


def main():
    source = (SOURCE / "q45_ceremony.erl").read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="q45-ceremony-") as tmp:
        directory = Path(tmp)
        baseline = run_suite(source, directory)
        print(baseline.stdout, end="")
        if baseline.returncode:
            raise SystemExit(baseline.stderr or "baseline failed")
        for name, witness, original, replacement in MUTANTS:
            if source.count(original) != 1:
                raise SystemExit(f"{name}: expected one mutation site")
            mutant = run_suite(source.replace(original, replacement, 1), directory)
            failure = rf"q45_ceremony_tests: {re.escape(witness)}\.\.\.\*failed\*"
            if mutant.returncode != 1 or not re.search(failure, mutant.stdout):
                raise SystemExit(f"{name}: expected {witness} to fail\n{mutant.stdout}{mutant.stderr}")
            print(f"Rejected {name} ({witness})")
    print(f"{len(MUTANTS)}/{len(MUTANTS)} compiled mutants rejected")


if __name__ == "__main__":
    main()
