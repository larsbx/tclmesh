"""Runner guard regressions using disposable Git repos and fake tools only.

No Lean, Quint, TLC or replay bank is executed by this module. The fake Lean
commands exercise receipt finalization; their output is not acceptance evidence.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
GIT = shutil.which('git')


@unittest.skipUnless(GIT, 'Git is required for disposable-checkout regressions')
class CheckoutGuard(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sandbox = tempfile.TemporaryDirectory(prefix='q45-checkout-tests-')
        cls.base = Path(cls.sandbox.name)
        cls.template = cls.base / 'template'
        cls.template.mkdir()
        for folder in ('formal', 'spec', 'tools', 'tests', 'experiments/threshold_q45'):
            shutil.copytree(ROOT / folder, cls.template / folder,
                            ignore=shutil.ignore_patterns('__pycache__', 'node_modules', '.lake'))
        shutil.copy2(ROOT / '.gitignore', cls.template / '.gitignore')
        cls.env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
        cls.env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                       GIT_AUTHOR_NAME='Q45 regression', GIT_AUTHOR_EMAIL='q45@example.invalid',
                       GIT_COMMITTER_NAME='Q45 regression', GIT_COMMITTER_EMAIL='q45@example.invalid')
        cls.git_at(cls.template, 'init', '-q')
        cls.git_at(cls.template, 'add', '.')
        cls.git_at(cls.template, 'commit', '-qm', 'Disposable regression fixture')

    @classmethod
    def tearDownClass(cls):
        cls.sandbox.cleanup()

    @classmethod
    def git_at(cls, root, *args):
        return subprocess.check_output([GIT, '-C', str(root), *args], env=cls.env,
                                       text=True, stderr=subprocess.STDOUT).strip()

    def git(self, *args):
        return self.git_at(self.repo, *args)

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(dir=self.base)
        self.addCleanup(self.tmp.cleanup)
        self.work = Path(self.tmp.name)
        self.repo = self.work / 'repo'
        self.git_at(self.work, 'clone', '-q', '--local', str(self.template), str(self.repo))
        self.sha = self.git('rev-parse', 'HEAD')
        self.out = self.work / 'results'
        self.marker = self.work / 'tool-launches'
        self.bin = self.work / 'bin'
        self.bin.mkdir()
        self.run_env = dict(self.env, PATH=str(self.bin) + os.pathsep + os.environ['PATH'],
                            Q45_FAKE_MARKER=str(self.marker), Q45_FAKE_REPO=str(self.repo),
                            Q45_REAL_GIT=GIT)
        # Each stub records invocation. Only expected runner diagnostics are
        # synthesized; real test runtimes are never invoked.
        stub = '''#!PYTHON
import json, os, pathlib, subprocess, sys
root = pathlib.Path(os.environ['Q45_FAKE_REPO'])
with open(os.environ['Q45_FAKE_MARKER'], 'a') as f:
    f.write(pathlib.Path(sys.argv[0]).name + ' ' + repr(sys.argv[1:]) + '\\n')
if pathlib.Path(sys.argv[0]).name == 'lean':
    print('Lean (version 4.35.0, regression fake)')
elif sys.argv[1:3] == ['env', 'lean']:
    if '/reject/' in sys.argv[-1]:
        print('Tactic `decide` proved that the proposition is false')
        sys.exit(1)
    bank = json.loads((root / 'formal/testbanks/manifest.json').read_text())
    print('Q45_LEAN_TESTBANK: 20 cases; standard axioms only')
    for c in bank['cases']:
        if 'declaration' in c:
            print(c['declaration'])
elif sys.argv[1:] == ['build']:
    mode = os.environ.get('Q45_FAKE_MUTATION')
    if mode == 'source':
        with (root / 'formal/testbanks/lean/Positive.lean').open('a') as f:
            f.write('\\n-- changed during fake execution\\n')
    elif mode == 'head':
        subprocess.run([os.environ['Q45_REAL_GIT'], '-C', str(root), 'commit',
                        '--allow-empty', '-qm', 'Changed HEAD during fake execution'], check=True)
    elif mode == 'metadata':
        (root / '.git').rename(root / '.git-unavailable')
    elif mode == 'untracked':
        (root / 'unexpected-source.txt').write_text('unexpected')
    elif mode == 'hash-error':
        (root / 'spec/lean-toolchain').unlink()
'''.replace('PYTHON', sys.executable)
        for name in ('lean', 'lake'):
            p = self.bin / name
            p.write_text(stub)
            p.chmod(0o755)

    def cli(self, action='run', revision=True, extra=()):
        argv = [sys.executable, '-B', str(self.repo / 'tools/run_q45_testbanks.py'),
                action, '--suite', 'lean']
        if action == 'run':
            argv += ['--out', str(self.out)]
        if revision is True:
            argv += ['--revision', self.sha]
        elif revision is not False:
            argv += ['--revision=' + revision]
        return subprocess.run(argv + list(extra), cwd=self.repo, env=self.run_env,
                              capture_output=True, text=True, timeout=20)

    def rejected_before_tools(self, revision=True, diagnostic=None):
        result = self.cli(revision=revision)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        if diagnostic:
            self.assertIn(diagnostic, result.stderr)
        self.assertFalse(self.marker.exists(), 'a test tool ran before checkout admission')
        self.assertFalse(self.out.exists(), 'invalid checkout created a result/acceptance receipt')

    def test_explicit_full_commit_required(self):
        for revision in (False, 'HEAD', self.sha[:12], 'main', '-' * 40):
            with self.subTest(revision=revision):
                self.rejected_before_tools(revision, 'exact 40-character commit SHA')

    def test_unknown_commit_rejected(self):
        self.rejected_before_tools('0' * 40, 'Git metadata unavailable')

    def test_wrong_existing_commit_rejected_even_with_identical_sources(self):
        self.git('commit', '--allow-empty', '-qm', 'Different revision; same files')
        self.rejected_before_tools(diagnostic='checkout revision mismatch')

    def test_unstaged_tracked_source_rejected(self):
        with (self.repo / 'formal/testbanks/lean/Positive.lean').open('a') as f:
            f.write('\n-- unreviewed edit\n')
        self.rejected_before_tools(diagnostic='dirty checkout')

    def test_staged_source_rejected(self):
        (self.repo / 'formal/testbanks/lean/Positive.lean').write_text('-- replaced\n')
        self.git('add', 'formal/testbanks/lean/Positive.lean')
        self.rejected_before_tools(diagnostic='dirty checkout')

    def test_tracked_deletion_rejected(self):
        (self.repo / 'tools/check_q45_adversarial.py').unlink()
        self.rejected_before_tools(diagnostic='dirty checkout')

    def test_untracked_source_cannot_be_hidden_by_status_config(self):
        self.git('config', 'status.showUntrackedFiles', 'no')
        (self.repo / 'unreviewed.py').write_text('print("unreviewed")\n')
        self.rejected_before_tools(diagnostic='dirty checkout')

    def test_submodule_dirt_cannot_be_hidden_by_status_config(self):
        self.git('-c', 'protocol.file.allow=always', 'submodule', 'add', '-q',
                 str(self.template), 'dependency')
        self.git('commit', '-qam', 'Add fixture submodule')
        self.sha = self.git('rev-parse', 'HEAD')
        self.git('config', 'submodule.dependency.ignore', 'all')
        (self.repo / 'dependency/unreviewed.py').write_text('unreviewed\n')
        self.rejected_before_tools(diagnostic='dirty checkout')

    def test_missing_git_executable_rejected(self):
        self.run_env['PATH'] = str(self.bin)
        self.rejected_before_tools(diagnostic='Git metadata unavailable')

    def test_source_archive_without_git_metadata_rejected(self):
        shutil.rmtree(self.repo / '.git')
        self.rejected_before_tools(diagnostic='Git metadata unavailable')

    def test_broken_git_metadata_rejected(self):
        shutil.rmtree(self.repo / '.git')
        (self.repo / '.git').write_text('gitdir: /nonexistent/q45-git-metadata\n')
        self.rejected_before_tools(diagnostic='Git metadata unavailable')

    def test_parent_repository_is_not_valid_metadata(self):
        shutil.rmtree(self.repo / '.git')
        self.git_at(self.work, 'init', '-q')
        self.rejected_before_tools(diagnostic='checkout root does not match')

    def test_failed_git_status_with_empty_stdout_is_not_clean(self):
        wrapper = self.bin / 'git'
        wrapper.write_text(f'#!{sys.executable}\nimport os, sys\n'
                           'if sys.argv[1] == "status":\n'
                           '    sys.exit(73)\n'
                           'os.execv(os.environ["Q45_REAL_GIT"], '
                           '[os.environ["Q45_REAL_GIT"], *sys.argv[1:]])\n')
        wrapper.chmod(0o755)
        self.rejected_before_tools(diagnostic='Git metadata unavailable (status')

    def test_validate_and_plan_need_no_revision_git_or_test_tools(self):
        shutil.rmtree(self.repo / '.git')
        self.run_env['PATH'] = str(self.bin)
        for action in ('validate', 'plan'):
            with self.subTest(action=action):
                result = self.cli(action, revision=False, extra=['--suite', 'all'])
                self.assertEqual(result.returncode, 0, result.stderr)
                data = json.loads(result.stdout)
                self.assertEqual(data['status'], 'structurally_valid_not_executed')
                self.assertEqual((data['cases'], data['tasks']), (78, 22))
        self.assertFalse(self.marker.exists())
        self.assertFalse(self.out.exists())

    def test_clean_detached_checkout_and_uppercase_sha_admitted(self):
        self.git('checkout', '--detach', '-q', self.sha)
        # Ignored installed dependencies do not make an otherwise clean tree dirty.
        cache = self.repo / 'formal/quint/node_modules/fake-cache'
        cache.parent.mkdir(parents=True)
        cache.write_text('ignored dependency cache')
        result = self.cli(revision=self.sha.upper())
        self.assertEqual(result.returncode, 0, result.stderr)
        receipt = json.loads((self.out / 'receipt.json').read_text())
        self.assertEqual(receipt['status'], 'passed')
        self.assertEqual(receipt['case_counts']['passed'], 28)
        self.assertEqual(receipt['git'], {'expected_revision': self.sha,
                                         'revision': self.sha, 'dirty': False})
        self.assertEqual(receipt['git_final'], receipt['git'])
        self.assertFalse(receipt['source_changed_during_run'])

    def test_manual_workflow_ignored_output_directory_remains_usable(self):
        self.out = self.repo / 'q45-server-results/manual-001'
        result = self.cli()
        self.assertEqual(result.returncode, 0, result.stderr)
        receipt = json.loads((self.out / 'receipt.json').read_text())
        self.assertEqual(receipt['status'], 'passed')
        self.assertEqual(receipt['git_final'], receipt['git'])

    def test_invalid_end_state_cannot_produce_successful_receipt(self):
        for mutation in ('source', 'head', 'metadata', 'untracked', 'hash-error'):
            with self.subTest(mutation=mutation):
                self.out = self.work / ('results-' + mutation)
                self.run_env['Q45_FAKE_MUTATION'] = mutation
                result = self.cli()
                self.assertNotEqual(result.returncode, 0, result.stdout)
                receipt = json.loads((self.out / 'receipt.json').read_text())
                self.assertEqual(receipt['status'], 'failed')
                self.assertTrue(receipt['checkout_changed_during_run'])
                self.assertEqual(receipt['source_changed_during_run'], mutation in {'source', 'hash-error'})
                if mutation == 'metadata':
                    (self.repo / '.git-unavailable').rename(self.repo / '.git')
                self.git('reset', '--hard', self.sha)
                if mutation == 'untracked':
                    (self.repo / 'unexpected-source.txt').unlink()


if __name__ == '__main__':
    unittest.main()
