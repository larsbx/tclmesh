"""Check Lean + Quint/TLC boundaries, expected counterexamples and actor replay.

Prerequisites: pinned spec/Lean toolchain on PATH, Node/npm, Java 21, OTP,
and `npm ci --ignore-scripts --prefix formal/quint`. No silent reduced mode.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / 'formal/quint'
QUINT = str(MODEL / 'node_modules/.bin/quint')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--evidence-dir', type=Path)
    args = parser.parse_args()
    checks = []

    def check(name, cmd, cwd=ROOT, counterexample=False, timeout=180):
        print(f'Checking {name}...', flush=True)
        result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        output = result.stdout + result.stderr
        if counterexample:
            ok = (result.returncode != 0 and 'error: found a counterexample' in output
                  and 'Error: Invariant' in output and 'is violated' in output)
        else:
            ok = result.returncode == 0
        if not ok:
            print(output, file=sys.stderr)
            raise SystemExit(f'{name}: unexpected result {result.returncode}')
        record = {'name': name, 'exit_code': result.returncode,
                  'expectation': 'counterexample' if counterexample else 'success',
                  'output_sha256': hashlib.sha256(output.encode()).hexdigest()}
        count = re.search(r'([\d,]+) states generated, ([\d,]+) distinct states found', output)
        if count:
            record.update(states_generated=int(count[1].replace(',', '')),
                          distinct_states=int(count[2].replace(',', '')))
        audit = re.search(r'audited \d+ declarations \(\d+ theorems\): standard axioms only', output)
        if audit:
            record['axiom_audit'] = audit[0]
        if args.evidence_dir:
            args.evidence_dir.mkdir(parents=True, exist_ok=True)
            (args.evidence_dir / f'{name}.txt').write_text(output, encoding='utf-8')
        checks.append(record)
        print(f'  {name}: expected {record["expectation"]}', flush=True)
        return output

    lean_version = check('lean-version', ['lean', '--version'], ROOT / 'spec')
    if 'version 4.35.0,' not in lean_version:
        raise SystemExit('requires the exact spec/lean-toolchain version')
    check('lean-build', ['lake', 'build'], ROOT / 'spec')
    check('lean-axioms', ['lake', 'env', 'lean', 'Audit.lean'], ROOT / 'spec')
    quint_version = check('quint-version', [QUINT, '--version'], MODEL).strip()
    if quint_version != '0.33.1':
        raise SystemExit('requires pinned Quint 0.33.1')
    for model in ['q45_ceremony', 'q45_setup_views']:
        check(f'{model}-typecheck', [QUINT, 'typecheck', f'{model}.qnt'], MODEL)
        check(f'{model}-tests', [QUINT, 'test', f'{model}.qnt', '--backend=typescript',
                               '--max-samples=1', '--seed=0x45'], MODEL)

    def verify(name, model, invariant, init='init', negative=False):
        output = check(name, [QUINT, 'verify', f'{model}.qnt', '--backend=tlc',
            '--apalache-version=0.62.4', '--tlc-config=tlc.json', '--verbosity=3',
            f'--init={init}', f'--invariant={invariant}'], MODEL, negative)
        if not negative and ('Model checking completed. No error has been found.' not in output
                             or '0 states left on queue' not in output):
            raise SystemExit(f'{name}: exhaustive TLC completion was not recorded')
        return output

    verify('ceremony-safety', 'q45_ceremony', 'safety')
    verify('strict-contract', 'q45_ceremony', 'safety and outputIntegrity', 'initStrict')
    verify('ceremony-integrity-counterexample', 'q45_ceremony', 'outputIntegrity', negative=True)
    verify('setup-local-safety', 'q45_setup_views', 'localSafety')
    verify('setup-agreement-counterexample', 'q45_setup_views', 'agreement', negative=True)
    verify('setup-relabeling-counterexample', 'q45_setup_views', 'noRelabeling', negative=True)
    projection = [sys.executable, '-B', 'tools/check_q45_quint_projection.py']
    if args.evidence_dir:
        projection += ['--trace', str(args.evidence_dir.resolve() / 'quint-attack.itf.json')]
    check('quint-p2b-actor-projection', projection)
    paths = ['spec/lean-toolchain', 'spec/TclMesh/Q45Adversarial.lean', 'spec/TclMesh.lean',
        'spec/Audit.lean', 'formal/quint/package.json', 'formal/quint/package-lock.json',
        'formal/quint/q45_ceremony.qnt', 'formal/quint/q45_setup_views.qnt',
        'formal/quint/tlc.json', 'tools/check_q45_formal.py', 'tools/check_q45_quint_projection.py',
        'tools/q45_adversarial_probe.py', 'tools/q45_collective_setup.py',
        'tools/q45_collective_relin.py', 'tools/q45_oracle.py',
        'experiments/threshold_q45/q45_ceremony.erl',
        'experiments/threshold_q45/q45_quint_replay.erl']
    receipt = {'schema': 'q45-lean-quint-v1', 'checks': checks,
        'versions': {'lean': lean_version.strip(), 'quint': quint_version, 'apalache': '0.62.4'},
        'scope': 'Abstract-model proofs, finite TLC checks and one concrete generated trace; no FHE security or universal refinement proof.',
        'sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}}
    if args.evidence_dir:
        receipt['evidence_sha256'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(args.evidence_dir.iterdir()) if p.is_file()
            and (args.receipt is None or p.resolve() != args.receipt.resolve())}
    text = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.receipt:
        args.receipt.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
