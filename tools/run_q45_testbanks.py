"""Plan or execute the Q45 testbanks on an operator-controlled server.

`validate` and `plan` perform structural reads only. Only the explicit `run`
subcommand invokes Lean, Quint, TLC or the toy replay. No installation occurs.
"""
import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import re
import signal
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'formal/testbanks/manifest.json'
QUINT = ROOT / 'formal/quint/node_modules/.bin/quint'
MODEL = ROOT / 'formal/quint'
KINDS = {'lean_build', 'lean_bank', 'lean_reject', 'quint_bank', 'tlc', 'projection', 'toy_replay'}


def source(path):
    p = (ROOT / path).resolve()
    if not p.is_relative_to(ROOT) or not p.is_file():
        raise ValueError(f'not a repository source file: {path}')
    return p


def load_bank():
    bank = json.loads(MANIFEST.read_text())
    if bank['schema'] != 'q45-testbanks-v1':
        raise ValueError('unsupported bank schema')
    tasks = {t['id']: t for t in bank['tasks']}
    cases = {c['id']: c for c in bank['cases']}
    if len(tasks) != len(bank['tasks']) or len(cases) != len(bank['cases']):
        raise ValueError('duplicate task/case ID')
    allowed = {
        'lean_bank': {'proof_checks'}, 'lean_reject': {'false_claim_rejected'},
        'quint_bank': {'scenario_passes'}, 'tlc': {'counterexample_found', 'exhaustive_safety'},
        'projection': {'concrete_trace_agrees'}, 'toy_replay': {'honest_and_adversarial_replay'},
    }
    for t in tasks.values():
        if not re.fullmatch(r'[a-z0-9-]+', t['id']) or t['kind'] not in KINDS:
            raise ValueError(f'invalid task: {t}')
        if t['suite'] not in {'lean', 'quint', 'replay'}:
            raise ValueError('unknown suite')
        if 'source' in t:
            text = source(t['source']).read_text()
            for c in cases.values():
                if c['task'] != t['id']:
                    continue
                if t['kind'] == 'lean_bank' and ('#check ' + c['declaration']) not in text:
                    raise ValueError(f'{c["id"]}: missing checked declaration')
                if t['kind'] == 'quint_bank' and not re.search(
                        r'\brun\s+' + re.escape(c['scenario']) + r'\s*=', text):
                    raise ValueError(f'{c["id"]}: missing scenario')
    for c in cases.values():
        if not re.fullmatch(r'[A-Z]{2}\d{3}', c['id']) or c['task'] not in tasks:
            raise ValueError(f'invalid case: {c}')
        t = tasks[c['task']]
        if c['expected'] not in allowed.get(t['kind'], set()):
            raise ValueError(f'{c["id"]}: invalid expectation for task kind')
        if t['kind'] == 'tlc' and t['counterexample'] != (c['expected'] == 'counterexample_found'):
            raise ValueError(f'{c["id"]}: inconsistent counterexample classification')
    for t in tasks.values():
        if t['kind'] != 'lean_build' and not any(c['task'] == t['id'] for c in cases.values()):
            raise ValueError(f'{t["id"]}: no acceptance cases')
    for suite, labels in bank['suites'].items():
        if suite not in {'lean', 'quint', 'all'} or not set(labels) <= {'lean', 'quint', 'replay'}:
            raise ValueError('invalid suite mapping')
    if bank['suites'] != {'lean': ['lean'], 'quint': ['quint'], 'all': ['lean', 'quint', 'replay']}:
        raise ValueError('suite mapping must not silently omit a bank')
    if bank['tasks'][0]['id'] != 'lean-build' or bank['tasks'][0]['kind'] != 'lean_build':
        raise ValueError('Lean build prerequisite must precede bank compilation')
    version = bank['versions']
    if (ROOT / 'spec/lean-toolchain').read_text().strip() != 'leanprover/lean4:v' + version['lean']:
        raise ValueError('Lean toolchain and manifest differ')
    package = json.loads((MODEL / 'package.json').read_text())
    lock = json.loads((MODEL / 'package-lock.json').read_text())
    if package['devDependencies']['@informalsystems/quint'] != version['quint'] or \
            lock['packages']['node_modules/@informalsystems/quint']['version'] != version['quint']:
        raise ValueError('Quint manifest/package/lock versions differ')
    return bank


def commands(t, cases, bank, seed):
    kind = t['kind']
    if kind == 'lean_build':
        return [(ROOT / 'spec', ['lake', 'clean']), (ROOT / 'spec', ['lake', 'build'])]
    if kind in {'lean_bank', 'lean_reject'}:
        return [(ROOT / 'spec', ['lake', 'env', 'lean', str(source(t['source']))])]
    if kind == 'quint_bank':
        path = str(source(t['source']))
        names = '|'.join(re.escape(c['scenario']) for c in cases)
        return [(MODEL, [str(QUINT), 'typecheck', path]),
                (MODEL, [str(QUINT), 'test', path, '--backend=typescript',
                         '--max-samples=1', f'--seed={seed}', f'--match=^({names})$'])]
    if kind == 'tlc':
        return [(MODEL, [str(QUINT), 'verify', str(source(t['source'])), '--backend=tlc',
            '--apalache-version=' + bank['versions']['apalache'],
            '--tlc-config=' + str(MODEL / 'tlc.json'), '--verbosity=3',
            '--init=' + t['init'], '--invariant=' + t['invariant']])]
    if kind == 'projection':
        return [(ROOT, [sys.executable, '-B', 'tools/check_q45_quint_projection.py', '--seed=' + seed])]
    return [(ROOT, [sys.executable, '-B', 'tools/check_q45_adversarial.py'])]


def satisfied(t, cases, code, stdout, stderr):
    output = stdout + stderr
    if t['kind'] == 'lean_reject':
        return code != 0 and bool(re.search(
            r'Tactic `decide` proved that the proposition.*?is false', output, re.S)) and not re.search(
            r'unknown identifier|unexpected token|object file .* does not exist|failed to synthesize',
            output, re.I)
    if t['kind'] == 'tlc':
        if t['counterexample']:
            return code != 0 and 'error: found a counterexample' in output and \
                bool(re.search(r'Error: Invariant .* is violated', output))
        return code == 0 and 'Model checking completed. No error has been found.' in output and \
            '0 states left on queue' in output
    if code != 0:
        return False
    if t['kind'] == 'lean_bank':
        return 'Q45_LEAN_TESTBANK: 20 cases; standard axioms only' in output and all(
            c['declaration'] in output for c in cases)
    if t['kind'] == 'quint_bank':
        return all(re.search(re.escape(c['scenario']) + r' passed 1 test\(s\)', output) for c in cases)
    if t['kind'] == 'projection':
        return '20 snapshots match' in output and 'Incorrect final-result projection rejected' in output
    if t['kind'] == 'toy_replay':
        try:
            r = json.loads(stdout)
            return r['actor_replay']['executed'] is True and \
                r['measurements']['threshold_cases'] == 640 and \
                r['measurements']['delta_bit_flips_accepted'] == 640 and \
                r['measurements']['margin_80_failures'] == 0 and \
                r['actor_replay']['honest_cases'] == 640 and \
                r['actor_replay']['canonical_bit_flip_completions'] == 640
        except (KeyError, ValueError, TypeError):
            return False
    return True


def inventory():
    paths = set()
    for folder, suffixes in [('spec', {'.lean', '.toml', '.json'}),
                             ('formal/testbanks', {'.lean', '.qnt', '.json', '.md'}),
                             ('formal/quint', {'.qnt'})]:
        for p in (ROOT / folder).rglob('*'):
            if p.is_file() and p.suffix in suffixes and not any(
                    part in {'.lake', 'node_modules', 'evidence', '_apalache-out'} for part in p.parts):
                paths.add(p)
    paths.update((ROOT / 'tools').glob('*q45*.py'))
    paths.update((ROOT / 'tests').glob('test_threshold_q45*.py'))
    paths.update((ROOT / 'experiments/threshold_q45').glob('*.erl'))
    paths.update(ROOT / p for p in ['spec/lean-toolchain', 'formal/quint/package.json',
        'formal/quint/package-lock.json', 'formal/quint/tlc.json'])
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def checked_checkout(revision):
    """Require an explicit commit and a clean tree; Git failures are never clean."""
    if not revision or not re.fullmatch(r'[0-9a-fA-F]{40}', revision):
        raise ValueError('run requires --revision as an exact 40-character commit SHA')
    revision = revision.lower()

    def git(*argv):
        try:
            result = subprocess.run(['git', *argv], cwd=ROOT, capture_output=True, text=True)
        except OSError as e:
            raise ValueError(f'Git metadata unavailable: {e}') from e
        if result.returncode != 0:
            raise ValueError(f'Git metadata unavailable ({" ".join(argv)}): {result.stderr.strip()}')
        return result.stdout.strip()

    if Path(git('rev-parse', '--show-toplevel')).resolve() != ROOT:
        raise ValueError('Git checkout root does not match the testbank repository')
    selected = git('rev-parse', '--verify', revision + '^{commit}')
    head = git('rev-parse', '--verify', 'HEAD^{commit}')
    if selected != revision or head != revision:
        raise ValueError(f'checkout revision mismatch: expected {revision}, found {head}')
    # Explicit options prevent local status configuration from hiding untracked
    # files or dirty submodules. Ignored tool caches/results remain permitted.
    dirty = git('status', '--porcelain=v1', '--untracked-files=all', '--ignore-submodules=none')
    if dirty:
        raise ValueError('dirty checkout: commit or remove tracked and untracked changes before running')
    return {'expected_revision': revision, 'revision': head, 'dirty': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['validate', 'plan', 'run'])
    parser.add_argument('--suite', choices=['lean', 'quint', 'all'], default='all')
    parser.add_argument('--seed', default='0x45')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--revision', help='required for run: exact reviewed 40-character commit SHA')
    parser.add_argument('--timeout', type=int, default=900, help='seconds per subprocess')
    args = parser.parse_args()
    if args.timeout <= 0 or int(args.seed, 0) < 0:
        parser.error('positive timeout and nonnegative integer seed required')
    if args.action == 'run':
        if args.out is None:
            parser.error('run requires --out pointing to a new result directory')
        try:
            checkout = checked_checkout(args.revision)
        except ValueError as e:
            parser.error(str(e))
    bank = load_bank()
    selected = [t for t in bank['tasks'] if t['suite'] in bank['suites'][args.suite]]
    cases = [c for c in bank['cases'] if any(c['task'] == t['id'] for t in selected)]
    planned = [{'task': t['id'], 'case_ids': [c['id'] for c in cases if c['task'] == t['id']],
        'commands': [{'cwd': str(cwd), 'argv': cmd} for cwd, cmd in commands(
            t, [c for c in cases if c['task'] == t['id']], bank, args.seed)]} for t in selected]
    if args.action != 'run':
        result = {'status': 'structurally_valid_not_executed', 'suite': args.suite,
                  'tasks': len(selected), 'cases': len(cases)}
        if args.action == 'plan':
            result['plan'] = planned
        print(json.dumps(result, indent=2))
        return
    out = args.out.resolve()
    if any(out.is_relative_to(ROOT / p) for p in ['spec', 'formal/testbanks', 'formal/quint']):
        parser.error('result directory must be separate from formal source files')
    out.mkdir(parents=True, exist_ok=False)
    now = lambda: dt.datetime.now(dt.timezone.utc).isoformat()
    receipt = {'schema': 'q45-server-testbank-receipt-v1', 'started_at': now(),
        'status': 'running', 'suite': args.suite, 'seed': args.seed,
        'scope': bank['scope'], 'host': {'hostname': platform.node(), 'platform': platform.platform(),
        'python': platform.python_version()}, 'source_sha256': inventory(),
        'git': checkout,
        'tasks': [], 'cases': [{**c, 'status': 'not_run'} for c in cases], 'preflight': []}

    def save():
        temporary = out / 'receipt.json.tmp'
        temporary.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n', encoding='utf-8')
        os.replace(temporary, out / 'receipt.json')

    def invoke(label, cwd, cmd):
        start = time.monotonic()
        record = {'label': label, 'cwd': str(cwd), 'argv': cmd, 'started_at': now()}
        try:
            process = subprocess.Popen(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE, start_new_session=os.name == 'posix')
            try:
                stdout, stderr = process.communicate(timeout=args.timeout)
                code = process.returncode
            except (subprocess.TimeoutExpired, KeyboardInterrupt) as e:
                record['timed_out' if isinstance(e, subprocess.TimeoutExpired) else 'interrupted'] = True
                # Stop the model-checker JVM as well as its CLI parent.
                def stop(sig):
                    try:
                        if os.name == 'posix':
                            os.killpg(process.pid, sig)
                        elif sig == signal.SIGTERM:
                            process.terminate()
                        else:
                            process.kill()
                    except ProcessLookupError:
                        pass
                stop(signal.SIGTERM)
                try:
                    stdout, stderr = process.communicate(timeout=5)
                except subprocess.TimeoutExpired:
                    stop(signal.SIGKILL)
                    stdout, stderr = process.communicate()
                code = -1
        except OSError as e:
            code, stdout, stderr = -1, '', str(e)
            record['launch_error'] = str(e)
        record.update(exit_code=code, elapsed_seconds=round(time.monotonic() - start, 3))
        for stream, value in [('stdout', stdout), ('stderr', stderr)]:
            name = f'{label}.{stream}.log'
            (out / name).write_text(value, encoding='utf-8')
            record[stream] = {'file': name, 'sha256': hashlib.sha256(value.encode()).hexdigest()}
        return record, stdout, stderr

    current = None
    save()
    try:
        need_lean = any(t['suite'] == 'lean' for t in selected)
        need_quint = any(t['suite'] == 'quint' for t in selected)
        need_replay = any(t['suite'] == 'replay' for t in selected)
        preflight = []
        if need_lean:
            preflight.append(('lean-version', ROOT / 'spec', ['lean', '--version'],
                lambda x: 'version ' + bank['versions']['lean'] + ',' in x))
        if need_quint or need_replay:
            preflight += [('quint-version', MODEL, [str(QUINT), '--version'],
                           lambda x: x.strip() == bank['versions']['quint']),
                          ('node-version', ROOT, ['node', '--version'],
                           lambda x: bool(re.search(r'^v(\d+)', x)) and int(re.search(r'^v(\d+)', x)[1]) >= 22)]
        if need_quint:
            preflight.append(('java-version', ROOT, ['java', '-version'],
                lambda x: bool(re.search(r'version "' + str(bank['versions']['java_major']) + r'[.\"]', x))))
        if need_replay:
            preflight.append(('otp-version', ROOT, ['erl', '-noshell', '-eval',
                'io:format("~s", [erlang:system_info(otp_release)]), halt(0).'],
                lambda x: x.strip().isdigit() and int(x.strip()) >= 25))
            if shutil.which('erlc') is None:
                raise RuntimeError('erlc is required for replay')
        for label, cwd, cmd, accept in preflight:
            record, stdout, stderr = invoke(label, cwd, cmd)
            receipt['preflight'].append(record)
            save()
            if record.get('interrupted'):
                raise KeyboardInterrupt
            if record['exit_code'] != 0 or not accept(stdout + stderr):
                raise RuntimeError(f'{label}: missing or incompatible prerequisite')
        for t in selected:
            task_cases = [c for c in cases if c['task'] == t['id']]
            current = {'id': t['id'], 'status': 'running', 'commands': []}
            receipt['tasks'].append(current)
            save()
            outputs = []
            for index, (cwd, cmd) in enumerate(commands(t, task_cases, bank, args.seed)):
                record, stdout, stderr = invoke(f'{t["id"]}-{index}', cwd, cmd)
                current['commands'].append(record)
                outputs.append((record, stdout, stderr))
                save()
                if record.get('interrupted'):
                    raise KeyboardInterrupt
                if record.get('timed_out') or record.get('launch_error'):
                    raise RuntimeError(f'{t["id"]}: timed out or could not start')
                if index + 1 < len(commands(t, task_cases, bank, args.seed)) and record['exit_code'] != 0:
                    raise RuntimeError(f'{t["id"]}: prerequisite command failed')
            record, stdout, stderr = outputs[-1]
            ok = satisfied(t, task_cases, record['exit_code'], stdout, stderr)
            current['status'] = 'passed' if ok else 'failed'
            for c in receipt['cases']:
                if c['task'] == t['id']:
                    c['status'] = current['status']
                    c['observed'] = c['expected'] if ok else 'unexpected_result'
            save()
            if not ok:
                raise RuntimeError(f'{t["id"]}: did not satisfy the declared expectation')
            print(f'{t["id"]}: expected outcome satisfied', flush=True)
        receipt['status'] = 'passed'
    except KeyboardInterrupt:
        receipt.update(status='interrupted', error='operator interruption')
        if current is not None and current['status'] == 'running':
            current['status'] = 'interrupted'
    except Exception as e:
        receipt.update(status='failed', error=str(e))
        if current is not None and current['status'] == 'running':
            current['status'] = 'failed'
    finally:
        # Timed-out/interrupted tasks are failures or incomplete, never counterexamples.
        for c in receipt['cases']:
            task = next((t for t in receipt['tasks'] if t['id'] == c['task']), None)
            if c['status'] == 'not_run' and task and task['status'] in {'failed', 'interrupted'}:
                c['status'] = task['status']
        receipt['finished_at'] = now()
        receipt['case_counts'] = {s: sum(c['status'] == s for c in receipt['cases'])
                                  for s in ['passed', 'failed', 'interrupted', 'not_run']}
        try:
            receipt['source_changed_during_run'] = inventory() != receipt['source_sha256']
            if receipt['source_changed_during_run']:
                receipt.update(status='failed', error='source files changed during execution')
        except Exception as e:
            receipt.update(status='failed', source_changed_during_run=True,
                           error=f'could not recheck source hashes: {e}')
        try:
            receipt['git_final'] = checked_checkout(args.revision)
        except ValueError as e:
            receipt.update(status='failed', checkout_changed_during_run=True,
                           checkout_error=str(e), error=f'checkout verification failed: {e}')
        save()
    print(str(out / 'receipt.json'))
    if receipt['status'] != 'passed':
        print(receipt.get('error', 'incomplete run'), file=sys.stderr)
        raise SystemExit(130 if receipt['status'] == 'interrupted' else 1)


if __name__ == '__main__':
    main()
