"""Replay Quint-generated attack traces against the actual P1 BEAM actor.

This checks selected finite traces, not a universal refinement theorem. Actual
P2b ciphertexts/80-bit partials replace the model's symbolic payload classes.
"""
import argparse
import json
import random
import subprocess
import tempfile
from pathlib import Path

import q45_adversarial_probe as A

ROOT = Path(__file__).resolve().parents[1]
QUINT = ROOT / 'formal/quint/node_modules/.bin/quint'
SOURCE = ROOT / 'experiments/threshold_q45'
PHASES = ['inputs', 'sealing', 'quorum', 'partials', 'result', 'complete', 'aborted']


def decode_itf(value):
    if isinstance(value, dict):
        if '#bigint' in value:
            return int(value['#bigint'])
        if '#set' in value:
            return frozenset(decode_itf(x) for x in value['#set'])
        return {k: decode_itf(v) for k, v in value.items() if k != '#meta'}
    return value


def erl_list(values):
    return '[' + ','.join(map(str, sorted(values))) + ']'


def raw_binary(*polynomials):
    # Hex decoding is done by Erlang's parser expression in generated terms
    # nowhere: file:consult admits data only, so use literal binary bytes.
    return '<<' + ','.join(str(b) for p in polynomials for c in p for b in c.to_bytes(16, 'big')) + '>>'


def snapshot(s, wrong_result=False):
    result = 0 if wrong_result and s['phase'] == 5 else s['result']
    sets = [erl_list(s[k]) for k in ['inputs', 'seals', 'commits', 'quorum', 'received']]
    return '{' + ','.join([PHASES[s['phase']], *sets, str(result)]) + '}'


def terms(states, wrong_result=False):
    assert len(states) == 20 and states[0]['phase'] == 0
    assert states[-1]['phase'] == 5 and states[-1]['result'] == 1
    assert len(states[-1]['bad']) == 1 and not states[-1]['malformed']
    f = A.fixture(A.Q.SEEDS[0])
    inputs, ct = A.ciphertext(f, A.Q.INPUTS[0], random.Random('Quint projection input'))
    quorum = states[-1]['quorum']
    parts = A.partials(f, quorum, ct, {i: random.Random(f'Quint projection partial:{i}') for i in quorum})
    assert A.Q.combine(ct, parts) == A.Q.zero()
    rows = ['{fixture,[' + ','.join(raw_binary(*c) for c in inputs) + '],'
            + raw_binary(*ct) + ',' + erl_list(quorum) + ',' + snapshot(states[0]) + '}.']
    for old, new in zip(states, states[1:]):
        event = None
        for key, tag in [('inputs', 'input'), ('seals', 'seal'), ('commits', 'commit'), ('received', 'partial')]:
            added = new[key] - old[key]
            if added:
                i, = added
                if tag == 'partial':
                    part = parts[i]
                    if i in new['bad']:
                        part = A.Q.padd(part, A.Q.const(A.Q.DELTA))
                    assert A.P.canonical_polynomial(part)
                    event = '{partial,' + str(i) + ',' + raw_binary(part) + '}'
                else:
                    event = '{' + tag + ',' + str(i) + '}'
                break
        if event is None:
            assert old['phase'] == 4 and new['phase'] == 5
            event = '{result,' + str(new['result']) + '}'
        rows.append('{' + event + ',' + snapshot(new, wrong_result) + '}.')
    return '\n'.join(rows) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', default='0x45')
    parser.add_argument('--trace', type=Path, help='also retain the generated ITF trace')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='q45-quint-projection-') as tmp:
        directory = Path(tmp)
        trace = directory / 'attack.itf.json'
        subprocess.run([str(QUINT), 'run', 'q45_ceremony.qnt', '--backend=typescript',
            '--step=attackStep', '--max-steps=19', '--max-samples=1', f'--seed={args.seed}',
            '--verbosity=0', f'--out-itf={trace}'], cwd=ROOT / 'formal/quint', check=True, timeout=30)
        data = json.loads(trace.read_text())
        states = [decode_itf(row['s']) for row in data['states']]
        if args.trace:
            args.trace.write_text(trace.read_text(), encoding='utf-8')
        good = directory / 'trace.terms'
        bad = directory / 'wrong-projection.terms'
        good.write_text(terms(states), encoding='ascii')
        bad.write_text(terms(states, wrong_result=True), encoding='ascii')
        subprocess.run(['erlc', '-Werror', '-o', str(directory), str(SOURCE / 'q45_ceremony.erl'),
                        str(SOURCE / 'q45_quint_replay.erl')], check=True, timeout=30)
        def run(path):
            return subprocess.run(['erl', '-noshell', '-pa', str(directory), '-eval',
                f'ok = q45_quint_replay:run("{path.name}"), halt(0).'], cwd=directory,
                text=True, capture_output=True, timeout=30)
        replay = run(good)
        if replay.returncode:
            raise RuntimeError(replay.stdout + replay.stderr)
        mutant = run(bad)
        if mutant.returncode == 0 or 'projection_mismatch' not in mutant.stdout + mutant.stderr:
            raise RuntimeError('incorrect projection was not rejected for the expected reason')
        print(replay.stdout.strip())
        print('Incorrect final-result projection rejected (projection_mismatch).')


if __name__ == '__main__':
    main()
