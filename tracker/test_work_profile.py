import contextlib
import io
import json
import math
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import work_profile as profile


def row(number, dependencies=()):
    return dict(id=f'M{number:06}', module=f'Fixture.M{number}',
                imports=[f'M{d:06}' for d in dependencies])


class WorkProfileTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.rows = [row(1), row(2, [1, 1]), row(3, [1]), row(4, [2, 3])]
        self.samples = {f'M{n:06}': [n * 10] for n in range(1, 5)}

    def inventory(self, modules=()):
        data = dict(identity=dict(profile.evidence.pins(), platform='aarch64-unknown-linux-gnu'),
                    modules=list(modules), worker_scope='test fixture, not a coordinator inventory')
        path = self.root / 'inventory.json'
        path.write_text(json.dumps(data))
        return path, data

    def cli(self, *arguments):
        with patch.object(profile.tasks, 'module_rows', return_value=iter(self.rows)), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            code = profile.main(list(map(str, arguments)))
        return code, json.loads(output.getvalue())

    def test_diamond_counts_shared_dependency_once_and_models_critical_path(self):
        result = profile.profile(self.rows, set(), self.samples, slots=2)
        model = result['idealized_model']
        self.assertEqual(result['missing_modules'], 4)
        self.assertEqual(result['missing_modules_by_depth'], {0: 1, 1: 2, 2: 1})
        self.assertEqual(result['longest_missing_dependency_chain_modules'], 3)
        self.assertEqual(model['total_module_seconds'], 100)
        self.assertEqual(model['weighted_critical_path_seconds'], 80)
        self.assertEqual(model['work_per_slot_seconds'], 50)
        self.assertEqual(model['idealized_lower_bound_seconds'], 80)
        self.assertEqual(model['critical_path_ids'], ['M000001', 'M000003', 'M000004'])
        self.assertEqual(model['kind'], 'observed_timing_model')
        self.assertNotIn('module_timings', result)

    def test_cached_middle_node_does_not_hide_missing_transitive_import(self):
        rows = [row(1), row(2, [1]), row(3, [2])]
        result = profile.profile(rows, {'M000002'}, {'M000001': [10], 'M000003': [30]}, slots=2)
        self.assertEqual(result['missing_modules'], 2)
        self.assertEqual(result['max_import_depth'], 2)
        self.assertEqual(result['longest_missing_dependency_chain_modules'], 2)
        self.assertEqual(result['idealized_model']['total_module_seconds'], 40)
        self.assertEqual(result['idealized_model']['weighted_critical_path_seconds'], 40)
        self.assertEqual(result['idealized_model']['critical_path_ids'], ['M000001', 'M000003'])

    def test_missing_durations_suppress_model_and_cached_timings_do_not_fill_gaps(self):
        result = profile.profile(self.rows, {'M000001'},
                                 {'M000001': [10], 'M000002': [20]}, slots=3)
        self.assertIsNone(result['idealized_model'])
        self.assertIn('Missing module durations', result['model_unavailable_reason'])
        self.assertEqual(result['timing_coverage']['timed_project_modules'], 2)
        self.assertEqual(result['timing_coverage']['timed_missing_modules'], 1)
        self.assertEqual(result['timing_coverage']['missing_without_timings'], 2)
        self.assertEqual(result['longest_missing_dependency_chain_modules'], 2)

    def test_explicit_assumption_is_labeled_and_never_replaces_observed_timings(self):
        result = profile.profile(self.rows, {'M000001'}, {'M000002': [20]},
                                 slots=2, assume_seconds=5)
        model = result['idealized_model']
        self.assertEqual(model['kind'], 'assumption_scenario')
        self.assertEqual(model['assumed_modules'], 2)
        self.assertEqual(model['assume_module_seconds'], 5)
        self.assertEqual(model['total_module_seconds'], 30)
        self.assertEqual(model['weighted_critical_path_seconds'], 25)

    def test_repeated_observations_use_module_median_without_duplicate_work(self):
        self.samples['M000001'] = [10, 30]
        result = profile.profile(self.rows, set(), self.samples, slots=2)
        self.assertEqual(result['timing_coverage']['observations'], 5)
        self.assertEqual(result['idealized_model']['total_module_seconds'], 110)
        self.assertEqual(result['idealized_model']['weighted_critical_path_seconds'], 90)
        exported = profile.profile(self.rows, set(), self.samples, include_module_timings=True)
        self.assertEqual(exported['module_timings']['M000001'],
                         {'median_seconds': 20, 'observations': 2})

    def test_all_cached_means_zero_modeled_source_work_not_full_verification(self):
        result = profile.profile(self.rows, {r['id'] for r in self.rows}, {}, slots=8)
        self.assertEqual(result['missing_modules'], 0)
        self.assertEqual(result['longest_missing_dependency_chain_modules'], 0)
        self.assertEqual(result['idealized_model']['effective_slots'], 0)
        self.assertEqual(result['idealized_model']['idealized_lower_bound_seconds'], 0)
        self.assertTrue(any('final fresh-kernel' in text for text in result['limitations']))

    def test_ansi_and_millisecond_timings_ignore_nonproject_modules_and_other_facets(self):
        path = self.root / 'build.log'
        path.write_text('\x1b[32m✔ [2/5] Built Fixture.M1 (250ms)\x1b[0m\n'
                        '✔ [3/5] Built Fixture.M2:olean (1.5s)\n'
                        '✔ [4/5] Built Fixture.M3 (0s)\n'
                        '✔ [5/5] Built Fixture.M4\n'
                        '✔ [6/7] Built Mathlib.Unknown (100s)\n'
                        '✔ [7/7] Built Fixture.M1:c.o (90ms)\n')
        samples = profile.parse_timings([path], {r['module']: r['id'] for r in self.rows})
        self.assertEqual(dict(samples), {'M000001': [0.25], 'M000002': [1.5], 'M000003': [0]})

    def test_bad_project_timings_are_rejected(self):
        path = self.root / 'build.log'
        for duration in ('-1s', 'NaNs', '3min'):
            with self.subTest(duration=duration):
                path.write_text(f'✔ [2/5] Built Fixture.M1 ({duration})\n')
                with self.assertRaisesRegex(ValueError, 'Invalid module timing'):
                    profile.parse_timings([path], {'Fixture.M1': 'M000001'})

    def test_invalid_slots_assumptions_and_graphs_are_rejected(self):
        for slots in (0, -1, 1.5, True):
            with self.subTest(slots=slots), self.assertRaisesRegex(ValueError, 'Slots'):
                profile.profile(self.rows, set(), {}, slots=slots)
        for seconds in (0, -1, math.inf, math.nan):
            with self.subTest(seconds=seconds), self.assertRaisesRegex(ValueError, 'positive and finite'):
                profile.profile(self.rows, set(), {}, assume_seconds=seconds)
        for rows in ([], [row(1), row(1)], [row(1, [2])], [row(1, [2]), row(2, [1])]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                profile.profile(rows, set(), {})

    def test_cli_rejects_bad_pins_unknown_inventory_ids_and_duplicate_ids(self):
        for changes, error in (({'identity': {'lean': 'bad'}}, 'pin mismatch'),
                               ({'modules': ['M999999']}, 'Unknown inventory IDs'),
                               ({'modules': ['M000001', 'M000001']}, 'duplicate module IDs')):
            with self.subTest(changes=changes):
                path, data = self.inventory()
                data.update(changes)
                path.write_text(json.dumps(data))
                code, report = self.cli(path)
                self.assertEqual(code, 2)
                self.assertEqual(report['status'], 'invalid')
                self.assertIn(error, report['error'])

    def test_cli_profiles_existing_files_and_preserves_explicit_worker_scope(self):
        path, _ = self.inventory(['M000001'])
        log = self.root / 'build.log'
        log.write_text('✔ [2/5] Built Fixture.M2 (4s)\n')
        before = path.read_bytes(), log.read_bytes()
        code, result = self.cli(path, '--log', log, '--slots', 3, '--include-module-timings')
        self.assertEqual(code, 0)
        self.assertIsNone(result['idealized_model'])
        self.assertIn('not a coordinator', result['inputs']['worker_scope'])
        self.assertEqual(result['module_timings'], {'M000002': {'median_seconds': 4, 'observations': 1}})
        self.assertEqual(result['inputs']['inventory'],
                         {'name': path.name, 'sha256': profile.tasks.digest(path)})
        self.assertEqual(result['inputs']['logs'][0]['name'], log.name)
        self.assertNotIn(str(self.root), json.dumps(result))
        self.assertEqual((path.read_bytes(), log.read_bytes()), before)
        code, result = self.cli(path, '--log', log, '--slots', 0)
        self.assertEqual(code, 2)
        self.assertEqual(result['status'], 'invalid')


if __name__ == '__main__':
    unittest.main()
