"""Run P2b adversarial tests and, optionally, the independent BEAM replay.

Requires Python 3; default additionally requires Erlang/OTP + EUnit + Crypto.
--python-only is an explicit reduced check, never a silent actor-test skip.
"""
import argparse
import hashlib
import json
import platform
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def write_transcripts(path, probe):
    with path.open('w', encoding='ascii') as out:
        def encode(*polynomials):
            return b''.join(c.to_bytes(16, 'big') for p in polynomials for c in p).hex()
        for seed, mask, bits, _, inputs, ct, quorum, parts, _ in probe.replay_cases():
            omitted, = set(probe.Q.PARTIES) - quorum
            out.write('\t'.join([str(seed), str(mask), str(omitted), str(probe.Q.reference(bits)),
                *(encode(*value) for value in inputs), encode(*ct),
                *(encode(parts[i]) for i in sorted(quorum))]) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--python-only', action='store_true')
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    sys.path.insert(0, str(ROOT / 'tests'))
    import test_threshold_q45_adversarial as tests
    suite = unittest.defaultTestLoader.loadTestsFromModule(tests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
    actor = {'executed': False}
    if not args.python_only:
        source = ROOT / 'experiments' / 'threshold_q45'
        with tempfile.TemporaryDirectory(prefix='q45-p2b-adversarial-') as tmp:
            directory = Path(tmp)
            write_transcripts(directory / 'transcripts.tsv', tests.A)
            subprocess.run(['erlc', '-Werror', '-o', str(directory),
                str(source / 'q45_ceremony.erl'), str(source / 'q45_toy_replay.erl')],
                check=True, timeout=30)
            replay = subprocess.run(['erl', '-noshell', '-pa', str(directory), '-eval',
                'ok = q45_toy_replay:run_p2b("transcripts.tsv"), halt(0).'],
                cwd=directory, text=True, capture_output=True, check=True, timeout=60)
            actor = {'executed': True, 'output': replay.stdout.strip(),
                     'honest_cases': 640, 'canonical_bit_flip_completions': 640,
                     'small_offset_completions': 640, 'malformed_payload_aborts': 4}
            actor['otp_release'] = subprocess.run(['erl', '-noshell', '-eval',
                'io:format("~s", [erlang:system_info(otp_release)]), halt(0).'],
                text=True, capture_output=True, check=True, timeout=30).stdout.strip()
    paths = ['tools/q45_adversarial_probe.py', 'tools/check_q45_adversarial.py',
             'tests/test_threshold_q45_adversarial.py', 'tools/q45_oracle.py',
             'tools/q45_collective_setup.py', 'tools/q45_collective_relin.py',
             'tests/test_threshold_q45_collective_setup.py',
             'tests/test_threshold_q45_collective_relin.py',
             'experiments/threshold_q45/q45_ceremony.erl',
             'experiments/threshold_q45/q45_ceremony_tests.erl',
             'experiments/threshold_q45/q45_toy_replay.erl']
    receipt = {'schema': 'q45-p2b-adversarial-v1', 'source_pr': 55,
        'source_revision': 'b5507710d9a1d2d81e8643803dcb7e3dfd7f1f1d',
        'python': platform.python_version(), 'python_tests': result.testsRun,
        'measurements': tests.MEASUREMENTS, 'actor_replay': actor,
        'governed_release_enabled': False,
        'claim': 'Toy counterexample replay only; no malicious-security claim.',
        'sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}}
    text = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.receipt:
        args.receipt.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
