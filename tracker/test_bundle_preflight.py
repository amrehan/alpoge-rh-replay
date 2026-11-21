import contextlib
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import bundle_preflight as preflight


class BundlePreflightTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def bundle(self, name, entries):
        path = self.root / (name + '.tar.gz')
        with tarfile.open(path, 'w:gz') as archive:
            for member, data in entries:
                if isinstance(member, str):
                    member = tarfile.TarInfo(member)
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))
        return path, hashlib.sha256(path.read_bytes()).hexdigest()

    def cli(self, *archives):
        arguments = [value for path, digest in archives
                     for value in ('--archive', str(path), digest)]
        with contextlib.redirect_stdout(io.StringIO()) as output:
            code = preflight.main(arguments)
        return code, json.loads(output.getvalue())

    def test_disjoint_archives_pass_without_extracting_or_reading_entire_files(self):
        first = self.bundle('first', [('lib/lean/Fixture/A.olean', b'a' * (2 * preflight.BLOCK))])
        second = self.bundle('second', [('ir/Fixture/B.c', b'b')])
        original = preflight.HashingReader.read
        sizes = []

        def read(reader, size=-1):
            self.assertGreater(size, 0)
            sizes.append(size)
            return original(reader, size)

        with patch.object(Path, 'read_bytes', side_effect=AssertionError('whole-file read')), \
                patch.object(tarfile.TarFile, 'extract', side_effect=AssertionError('extraction')), \
                patch.object(tarfile.TarFile, 'extractall', side_effect=AssertionError('extraction')), \
                patch.object(preflight.HashingReader, 'read', read):
            code, report = self.cli(first, second)
        self.assertTrue(sizes)
        self.assertLessEqual(max(sizes), preflight.BLOCK)
        self.assertEqual(code, 0)
        self.assertEqual(report['status'], 'clear')
        self.assertEqual(report['summary']['unique_members'], 2)
        self.assertEqual(report['summary']['overlapping_members'], 0)
        self.assertEqual([a['sha256'] for a in report['archives']], [first[1], second[1]])

    def test_identical_overlap_accepts_directories_leading_dot_and_unicode(self):
        directories = []
        for name in ('.', './lib/', './lib/lean/', './lib/lean/AutomorphicForms₂/', './ir/'):
            member = tarfile.TarInfo(name)
            member.type = tarfile.DIRTYPE
            directories.append((member, b''))
        first = self.bundle('first', directories + [
            ('./lib/lean/AutomorphicForms₂/X.olean', b'proof'),
            ('./ir/AutomorphicForms₂/X.c', b'code'),
        ])
        second = self.bundle('second', [
            ('lib/lean/AutomorphicForms₂/X.olean', b'proof'),
            ('ir/AutomorphicForms₂/X.c', b'code'),
        ])
        code, report = self.cli(first, second)
        self.assertEqual(code, 0)
        self.assertEqual(report['conflicts'], [])
        self.assertEqual(report['summary']['overlapping_members'], 2)
        self.assertEqual([a['members'] for a in report['archives']], [2, 2])

    def test_object_collisions_group_variants_and_report_trace_changes_separately(self):
        def entries(proof, trace):
            return [('lib/lean/Fixture/A.olean', proof), ('lib/lean/Fixture/A.trace', trace),
                    ('lib/lean/Fixture/A.ilean', b'same interface')]

        first = self.bundle('first', entries(b'proof-one', b'trace-one'))
        second = self.bundle('second', entries(b'proof-two', b'trace-two'))
        third = self.bundle('third', entries(b'proof-one', b'trace-one'))
        code, report = self.cli(first, second, third)
        self.assertEqual(code, 1)
        self.assertEqual(report['status'], 'conflicts')
        self.assertEqual(report['summary']['conflicting_members'], 1)
        self.assertEqual(report['summary']['differing_trace_members'], 1)
        self.assertEqual(report['summary']['overlapping_members'], 3)
        self.assertEqual(report['conflicts'][0]['module'], 'Fixture.A')
        variants = report['conflicts'][0]['files'][0]['variants']
        self.assertEqual({v['sha256']: v['archives'] for v in variants}, {
            hashlib.sha256(b'proof-one').hexdigest(): [0, 2],
            hashlib.sha256(b'proof-two').hexdigest(): [1],
        })
        self.assertEqual(report['trace_differences'][0]['files'][0]['path'],
                         'lib/lean/Fixture/A.trace')

    def test_trace_only_differences_are_informational(self):
        first = self.bundle('first', [('lib/lean/Fixture/A.trace', b'{"log":["/worker-a/A.lean"]}')])
        second = self.bundle('second', [('lib/lean/Fixture/A.trace', b'{"log":["/worker-b/A.lean"]}')])
        code, report = self.cli(first, second)
        self.assertEqual(code, 0)
        self.assertEqual(report['status'], 'metadata_differences')
        self.assertEqual(report['conflicts'], [])
        self.assertEqual(report['summary']['differing_trace_members'], 1)

    def test_generated_setup_input_differences_are_informational(self):
        first = self.bundle('first', [('ir/Fixture/A.setup.json', b'{"src":"/worker-a/A.lean"}')])
        second = self.bundle('second', [('ir/Fixture/A.setup.json', b'{"src":"/worker-b/A.lean"}')])
        code, report = self.cli(first, second)
        self.assertEqual(code, 0)
        self.assertEqual(report['status'], 'metadata_differences')
        self.assertEqual(report['conflicts'], [])
        self.assertEqual(report['setup_differences'][0]['module'], 'Fixture.A')
        self.assertEqual(report['summary']['differing_setup_members'], 1)

    def test_unsafe_or_out_of_scope_member_paths_are_rejected(self):
        valid = self.bundle('valid', [('lib/lean/Fixture/A.olean', b'a')])
        for name in ('../lib/lean/A.olean', '/lib/lean/A.olean',
                     'lib/lean/../A.olean', 'lib//lean/A.olean', 'lib/lean/./A.olean',
                     'lib\\lean\\A.olean', './../ir/A.c', 'lakefile.olean',
                     'lib/lean/A', 'C:/lib/lean/A.olean'):
            with self.subTest(name=name):
                invalid = self.bundle('invalid', [(name, b'bad')])
                code, report = self.cli(valid, invalid)
                self.assertEqual(code, 2)
                self.assertEqual(report['status'], 'invalid')

    def test_unsafe_directory_is_rejected(self):
        member = tarfile.TarInfo('lib/lean/../../outside/')
        member.type = tarfile.DIRTYPE
        invalid = self.bundle('invalid', [(member, b'')])
        valid = self.bundle('valid', [('lib/lean/A.olean', b'a')])
        code, report = self.cli(valid, invalid)
        self.assertEqual(code, 2)
        self.assertIn('Unsafe member path', report['error'])

    def test_symlinks_hardlinks_devices_and_fifos_are_rejected(self):
        valid = self.bundle('valid', [('lib/lean/A.olean', b'a')])
        for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.CHRTYPE,
                     tarfile.BLKTYPE, tarfile.FIFOTYPE):
            with self.subTest(kind=kind):
                member = tarfile.TarInfo('lib/lean/A.olean')
                member.type = kind
                member.linkname = '../../outside'
                invalid = self.bundle('invalid', [(member, b'')])
                code, report = self.cli(valid, invalid)
                self.assertEqual(code, 2)
                self.assertIn('Nonregular member', report['error'])

    def test_duplicate_files_including_leading_dot_aliases_are_rejected(self):
        valid = self.bundle('valid', [('lib/lean/A.olean', b'a')])
        for second_name in ('lib/lean/A.olean', './lib/lean/A.olean'):
            with self.subTest(second_name=second_name):
                invalid = self.bundle('invalid', [('lib/lean/A.olean', b'a'), (second_name, b'a')])
                code, report = self.cli(valid, invalid)
                self.assertEqual(code, 2)
                self.assertIn('Duplicate member path', report['error'])

    def test_archive_digest_mismatch_is_not_reported_as_a_collision(self):
        first = self.bundle('first', [('lib/lean/A.olean', b'a')])
        second = self.bundle('second', [('lib/lean/A.olean', b'different')])
        code, report = self.cli(first, (second[0], '0' * 64))
        self.assertEqual(code, 2)
        self.assertIn('Archive SHA-256 mismatch', report['error'])
        self.assertNotIn('conflicts', report)
        code, report = self.cli(first, (second[0], 'not-a-digest'))
        self.assertEqual(code, 2)
        self.assertIn('64 hexadecimal characters', report['error'])

    def test_malformed_and_truncated_archives_are_rejected(self):
        valid = self.bundle('valid', [('lib/lean/A.olean', b'a')])
        raw = valid[0].read_bytes()
        bad_footer = bytearray(raw)
        bad_footer[-8] ^= 1
        for data in (b'not gzip', gzip.compress(b'not a tar archive'), raw[:-4], bytes(bad_footer)):
            with self.subTest(data=data[:20]):
                path = self.root / 'broken.tar.gz'
                path.write_bytes(data)
                code, report = self.cli(valid, (path, hashlib.sha256(data).hexdigest()))
                self.assertEqual(code, 2)
                self.assertEqual(report['status'], 'invalid')

    def test_members_hidden_after_tar_end_marker_are_rejected(self):
        valid = self.bundle('valid', [('lib/lean/A.olean', b'a')])
        hidden = self.bundle('hidden', [('../outside.olean', b'hidden')])
        combined = gzip.compress(gzip.decompress(valid[0].read_bytes())
                                 + gzip.decompress(hidden[0].read_bytes()))
        path = self.root / 'combined.tar.gz'
        path.write_bytes(combined)
        code, report = self.cli(valid, (path, hashlib.sha256(combined).hexdigest()))
        self.assertEqual(code, 2)
        self.assertIn('Nonzero data after the tar end marker', report['error'])

    @unittest.skipUnless(os.environ.get('REPLAY_NATIVE_TEST'), 'requires the pinned native Lean toolchain')
    def test_real_lake_coherent_workers_and_conflicting_dependency_overlay(self):
        # A controlled environment-dependent elaborator models differing
        # artifacts for the same source. This is not the Google failure's cause.
        sources = {
            'Probe/Base.lean': 'import Lean\nopen Lean Elab Command\n'
                'run_cmd do\n  let variant ← IO.getEnv "REUSE_PROBE_VARIANT"\n'
                '  let n : Nat := if variant == some "b" then 8 else 7\n'
                '  elabCommand (← `(def probeMarker : Nat := $(quote n)))\n'
                'def probeBase : Nat := 7\n',
            'Probe/Left.lean': 'import Probe.Base\ndef probeLeft : Nat := probeBase + 1\n',
            'Probe/Right.lean': 'import Probe.Base\ndef probeRight : Nat := probeBase + 2\n',
            'Probe.lean': 'import Probe.Left\nimport Probe.Right\n'
                'theorem probeTrue : probeLeft + probeRight = 17 := rfl\n',
        }
        launcher = ['elan', 'run', 'leanprover/lean4:v4.33.1', 'lake']

        def lake(project, variant, no_build=False):
            command = launcher + (['--no-build'] if no_build else [])
            return subprocess.run(command + ['--no-cache', 'build', '+Probe:olean'],
                                  cwd=project, capture_output=True, text=True,
                                  env=dict(os.environ, REUSE_PROBE_VARIANT=variant, LEAN_NUM_THREADS='2'))

        projects = []
        bundles = []
        for variant in ('a', 'b'):
            project = self.root / variant
            project.mkdir()
            (project / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
            (project / 'lakefile.toml').write_text('name = "probe"\n[[lean_lib]]\nname = "Probe"\n')
            for name, source in sources.items():
                path = project / name
                path.parent.mkdir(exist_ok=True)
                path.write_text(source)
            for no_build in (False, True):
                result = lake(project, variant, no_build)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            build = project / '.lake/build'
            entries = [(str(path.relative_to(build)), path.read_bytes())
                       for path in sorted((build / 'lib/lean').rglob('*')) if path.is_file()]
            bundles.append(self.bundle('worker-' + variant, entries))
            projects.append(project)

        code, report = self.cli(*bundles)
        self.assertEqual(code, 1)
        self.assertIn('Probe.Base', [c['module'] for c in report['conflicts']])
        first = projects[0] / '.lake/build/lib/lean/Probe'
        second = projects[1] / '.lake/build/lib/lean/Probe'
        self.assertEqual((first / 'Base.ilean').read_bytes(), (second / 'Base.ilean').read_bytes())
        self.assertNotEqual((first / 'Base.olean').read_bytes(), (second / 'Base.olean').read_bytes())
        for path in second.glob('Base.*'):
            shutil.copy2(path, first / path.name)
        mixed = lake(projects[0], 'a', no_build=True)
        self.assertEqual(mixed.returncode, 3, mixed.stdout + mixed.stderr)
        self.assertIn('out-of-date', mixed.stdout + mixed.stderr)
        rebuilt = lake(projects[0], 'a')
        self.assertEqual(rebuilt.returncode, 0, rebuilt.stdout + rebuilt.stderr)
        self.assertIn('Built Probe.Left', rebuilt.stdout + rebuilt.stderr)
        self.assertIn('Built Probe.Right', rebuilt.stdout + rebuilt.stderr)


if __name__ == '__main__':
    unittest.main()
