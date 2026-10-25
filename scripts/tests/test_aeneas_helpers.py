import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]


def load(filename):
    spec = importlib.util.spec_from_file_location(filename, SCRIPTS / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


audit = load('aeneas-audit.py')
extract = load('aeneas-extract.py')


class AuditValidation(unittest.TestCase):
    def setUp(self):
        self.inventory = {'checked': [{'name': 'example.spec', 'module': 'Proofs.Example'}],
                          'recorder_mappings': [{'api': 'State::update', 'theorem': 'example.spec'}]}
        self.report = {'tool': {'proofs': [{'api': 'State::update', 'theorem': 'example.spec',
                                          'module': 'Proofs.Example', 'precondition': 'true'}]}}

    def test_valid_mapping_and_explicit_precondition(self):
        audit.validate(self.inventory, self.report)
        self.inventory['checked'][0]['precondition'] = 'input length fits'
        self.report['tool']['proofs'][0]['precondition'] = 'input length fits'
        audit.validate(self.inventory, self.report)

    def test_reject_mapping_module_and_condition_drift(self):
        for key in ('module', 'precondition', 'theorem'):
            with self.subTest(key=key):
                report = json.loads(json.dumps(self.report))
                report['tool']['proofs'][0][key] = 'different'
                with self.assertRaises(ValueError):
                    audit.validate(self.inventory, report)

    def test_reject_missing_duplicate_and_injected_names(self):
        for checked in ([], self.inventory['checked'] * 2,
                        [{'name': 'example.spec\naxiom bad : False', 'module': 'Proofs.Example'}]):
            with self.subTest(checked=checked), self.assertRaises(ValueError):
                audit.validate({'checked': checked})


class ExtractionValidation(unittest.TestCase):
    def run_extract(self, content, extra=False, options=None):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            config = root / 'config.json'
            config.write_text(json.dumps({'entries': ['crate::update'], 'llbc': 'example.llbc',
                                          'models': {'Example.lean': ['update']}, **(options or {})}))
            output = root / 'out'

            def fake_run(argv, **kwargs):
                if argv[0] == 'charon':
                    for symbol in (options or {}).get('charon_exclude', []):
                        self.assertEqual(argv[argv.index(symbol) - 1], '--exclude')
                    self.assertEqual('--remove-unused-clauses' in argv,
                                     bool(options and options.get('remove_unused_clauses')))
                    if options and options.get('local_scope'):
                        at = argv.index('crate')
                        self.assertEqual(argv[at - 1], '--opaque')
                        for symbol in options['local_scope']['include']:
                            self.assertIn(('--include', symbol), list(zip(argv, argv[1:])))
                    for symbol in (options or {}).get('dependency_include', []):
                        self.assertIn(('--include', symbol), list(zip(argv, argv[1:])))
                    if options and options.get('charon_opaque'):
                        for symbol in options['charon_opaque']:
                            at = argv.index(symbol)
                            self.assertEqual(argv[at - 1], '--opaque')
                    if options and options.get('foreign_impl_entries'):
                        for symbol in options['foreign_impl_entries']:
                            self.assertEqual(argv[argv.index(symbol) - 1], '--start-from')
                    if options and options.get('impl_entries'):
                        for symbol in options['impl_entries']:
                            self.assertEqual(argv[argv.index(symbol) - 1], '--start-from')
                    if options and options.get('charon_include'):
                        self.assertIn('--include', argv)
                        self.assertIn('core::net::ip_addr::Ipv4Addr', argv)
                        self.assertIn('--extract-opaque-bodies', argv)
                    (output / 'example.llbc').write_text('{}')
                else:
                    self.assertEqual('-rooted-declarations' in argv,
                                     bool(options and options.get('rooted_declarations')))
                    self.assertEqual('-filter-trait-methods' in argv,
                                     bool(options and options.get('rooted_declarations')))
                    (output / 'Example.lean').write_text(content)
                    if extra:
                        (output / 'Unexpected.lean').write_text('def unexpected := 0')

            with patch.object(extract.subprocess, 'run', side_effect=fake_run):
                try:
                    extract.extract(root, config, output)
                except ValueError:
                    self.assertFalse((output / 'extraction.json').exists())
                    raise
            self.assertEqual(json.loads((output / 'extraction.json').read_text())['status'],
                             'extracted-not-proved')
            with self.assertRaises(FileExistsError):
                extract.extract(root, config, output)

    def test_expected_output_and_no_overwrite(self):
        self.run_extract('def update : Nat := 0\n')

    def test_multiline_generated_definition_name(self):
        self.run_extract('def\n  update : Nat := 0\n')

    def test_reject_partial_or_missing_body(self):
        for content in ('axiom update : Nat\n', 'def update : Nat := by sorry\n', 'def other := 0\n'):
            with self.subTest(content=content), self.assertRaises(ValueError):
                self.run_extract(content)

    def test_reject_unexpected_model(self):
        with self.assertRaises(ValueError):
            self.run_extract('def update := 0\n', extra=True)

    def test_local_scope_keeps_body_and_axiom_checks(self):
        options = {'local_scope': {'opaque_crate': True, 'include': [
            'crate::buf::take::Take', 'crate::buf::take::new',
            'crate::buf::take::_::limit']}}
        self.run_extract('def update := 0\n', options=options)
        for content in ('axiom update : Nat\n', 'def other := 0\n',
                        'def update := by sorry\n'):
            with self.subTest(content=content), self.assertRaises(ValueError):
                self.run_extract(content, options=options)

    def test_local_scope_accepts_validated_trait_impl_methods(self):
        symbol = '{impl crate::Integer for _}::div_floor'
        options = {'impl_entries': [symbol], 'local_scope': {
            'opaque_crate': True, 'include': [symbol]}}
        self.run_extract('def update := 0\n', options=options)
        for bad in ('{impl crate::* for _}::div_floor',
                    '{impl other::Integer for _}::div_floor',
                    '{impl crate::Integer for *}::div_floor',
                    symbol + '\naxiom bad : False'):
            with self.subTest(symbol=bad), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options={'local_scope': {
                    'opaque_crate': True, 'include': [bad]}})

    def test_impl_only_roots_and_empty_combined_selection(self):
        self.run_extract('def update := 0\n', options={
            'entries': [], 'impl_entries': ['{impl crate::Integer for _}::is_even']})
        with self.assertRaises(ValueError):
            self.run_extract('def update := 0\n', options={'entries': []})

    def test_dependency_bodies_are_selected_and_still_checked(self):
        options = {'dependency_include': [
            '{impl num_traits::identities::Zero for _}::is_zero',
            'num_traits::identities::Zero']}
        self.run_extract('def update := 0\n', options=options)
        with self.assertRaises(ValueError):
            self.run_extract('axiom update : Nat\n', options=options)
        for bad in ('num_traits::*', '{impl num_traits::* for _}::zero',
                    '{impl crate::Integer for _}::div_floor',
                    'num_traits::Zero\naxiom bad : False', 4):
            with self.subTest(symbol=bad), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options={'dependency_include': [bad]})

    def test_remove_unused_clauses_keeps_body_checks(self):
        options = {'remove_unused_clauses': True}
        self.run_extract('def update := 0\n', options=options)
        self.run_extract('def update := 0\n', options={'remove_unused_clauses': False})
        for content in ('axiom update : Nat\n', 'def other := 0\n',
                        'def update := by sorry\n'):
            with self.subTest(content=content), self.assertRaises(ValueError):
                self.run_extract(content, options=options)
        for value in ('true', 1, None, []):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options={'remove_unused_clauses': value})

    def test_rooted_and_exact_exclusion_keep_body_checks(self):
        options = {'rooted_declarations': True,
                   'charon_exclude': ['crate::buf::buf_mut::BufMut']}
        self.run_extract('def update := 0\n', options=options)
        self.run_extract('def update := 0\n', options={'rooted_declarations': False})
        for content in ('axiom update : Nat\n', 'def other := 0\n',
                        'def update := by sorry\n'):
            with self.subTest(content=content), self.assertRaises(ValueError):
                self.run_extract(content, options=options)
        for value in ('true', 1, None, []):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options={'rooted_declarations': value})
        for value in ('crate::BufMut', ['crate::*'], ['crate::_::field'],
                      ['--opaque'], ['crate::BufMut\n'], [1]):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options={'charon_exclude': value})

    def test_reject_invalid_local_scope(self):
        invalid = [False, [], {}, {'opaque_crate': False, 'include': ['crate::update']},
                   {'opaque_crate': True, 'include': 'crate::update'},
                   {'opaque_crate': True, 'include': []},
                   {'opaque_crate': True, 'include': ['crate::update'], 'extra': True}]
        invalid += [{'opaque_crate': True, 'include': [symbol]} for symbol in (
            'core::update', 'crate', 'crate::*', 'crate::buf::_',
            'crate::buf::take::**::limit', 'crate::update --include crate',
            'crate::update\n', '--opaque', 1)]
        for local_scope in invalid:
            with self.subTest(local_scope=local_scope), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options={'local_scope': local_scope})
        with self.assertRaises(ValueError):
            self.run_extract('def update := 0\n', options={
                'local_scope': {'opaque_crate': True, 'include': ['crate::update']},
                'extract_opaque_bodies': True})

    def test_concrete_dependency_extraction_keeps_axiom_filter(self):
        options = {'charon_include': ['core::net::ip_addr::Ipv4Addr'],
                   'extract_opaque_bodies': True}
        self.run_extract('def update := 0\n', options=options)
        with self.assertRaises(ValueError):
            self.run_extract('axiom address : Type\ndef update := 0\n', options=options)

    def test_reject_invalid_dependency_options(self):
        for options in ({'charon_include': ['--opaque']},
                        {'charon_include': ['crate::*']},
                        {'charon_include': 'core::net'},
                        {'extract_opaque_bodies': 'true'}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options=options)

    def test_local_trait_impl_selection_keeps_body_checks(self):
        options = {'impl_entries': ['{impl crate::net::Contains for _}::contains']}
        self.run_extract('def update := 0\n', options=options)
        with self.assertRaises(ValueError):
            self.run_extract('axiom unresolved : Type\ndef update := 0\n', options=options)

    def test_local_trait_concrete_std_receiver(self):
        options = {'impl_entries': ['{impl crate::ipext::IpBitAnd for core::net::ip_addr::Ipv4Addr}::bitand']}
        self.run_extract('def update := 0\n', options=options)
        with self.assertRaises(ValueError):
            self.run_extract('axiom unresolved : Type\ndef update := 0\n', options=options)

    def test_reject_foreign_or_unconstrained_impl_selectors(self):
        for entry in ('{impl core::cmp::Ord for _}::cmp', '{impl _ for _}::_',
                      '{impl crate::Contains for _}::contains --opaque',
                      '{impl crate::Contains for _}::contains\n'):
            with self.subTest(entry=entry), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options={'impl_entries': [entry]})

    def test_concrete_foreign_trait_selection_keeps_body_checks(self):
        options = {'foreign_impl_entries': ['{impl core::iter::traits::iterator::Iterator for crate::ipext::Ipv4AddrRange}::next']}
        self.run_extract('def update := 0\n', options=options)
        with self.assertRaises(ValueError):
            self.run_extract('axiom unresolved : Type\ndef update := 0\n', options=options)

    def test_reject_broad_or_injected_foreign_trait_selectors(self):
        for entry in ('{impl core::cmp::Ord for _}::cmp',
                      '{impl core::cmp::Ord for core::net::Ipv4Addr}::cmp',
                      '{impl _ for crate::Range}::next',
                      '{impl core::Iterator for crate::Range}::_',
                      '{impl core::Iterator for crate::Range}::next --opaque',
                      '{impl core::Iterator for crate::Range}::next\n'):
            with self.subTest(entry=entry), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options={'foreign_impl_entries': [entry]})

    def test_concrete_std_model_selection_keeps_axiom_filter(self):
        options = {'charon_opaque': [
            'core::net::ip_addr::{impl core::cmp::Ord for core::net::ip_addr::Ipv4Addr}::cmp',
            'core::net::ip_addr::{impl core::net::ip_addr::Ipv6Addr}::segments',
            'core::net::ip_addr::Ipv6Addr::segments',
            'core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::new',
        ]}
        self.run_extract('def update := 0\n', options=options)
        with self.assertRaises(ValueError):
            self.run_extract('axiom unresolved : Type\ndef update := 0\n', options=options)

    def test_reject_broad_local_or_injected_opaque_selectors(self):
        for symbol in ('crate::net::contains', 'core::*',
                       'core::net::{impl core::cmp::Ord for _}::cmp',
                       'core::net::{crate::Address}::new',
                       'crate::net::{core::net::Address}::new',
                       'core::net::{core::net::_}::new',
                       'core::net::{core::net::Address}::*',
                       'core::net::{core::net::Address}::new --include crate',
                       'core::net::{core::net::Address}::new\n',
                       'core::net::Address::cmp --include crate',
                       'core::net::Address::cmp\n'):
            with self.subTest(symbol=symbol), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options={'charon_opaque': [symbol]})
        for options in ({'charon_opaque': 'core::net::Address::cmp'},
                        {'charon_opaque': ['core::net::Address::cmp'],
                         'extract_opaque_bodies': True}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                self.run_extract('def update := 0\n', options=options)


if __name__ == '__main__':
    unittest.main()
