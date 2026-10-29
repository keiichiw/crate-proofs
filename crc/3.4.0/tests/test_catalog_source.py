"""Registry source identity follows the current Cargo lock and archive."""
from pathlib import Path
import hashlib
import importlib.util
import io
import json
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch
SCRIPT=Path(__file__).resolve().parents[1]/'aeneas/profiles/default/adapter/verify.py'
spec=importlib.util.spec_from_file_location('crc_catalog',SCRIPT)
adapter=importlib.util.module_from_spec(spec);spec.loader.exec_module(adapter)

class CatalogSource(unittest.TestCase):
    def test_locked_archive_rejects_missing_extra_and_changed_source(self):
        for mutation in ('none','missing','extra','changed','archive'):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as temporary:
                root=Path(temporary);installed=root/'registry';installed.mkdir()
                files={'Cargo.toml':b'[package]\n','src/lib.rs':b'pub const VALUE: u8 = 1;\n'}
                archive=root/'catalog.crate'
                with tarfile.open(archive,'w:gz') as tar:
                    for name,data in files.items():
                        info=tarfile.TarInfo('crc-catalog-0.0.1/'+name);info.size=len(data);info.mode=0o644
                        tar.addfile(info,io.BytesIO(data))
                        p=installed/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
                digest=hashlib.sha256(archive.read_bytes()).hexdigest()
                cache=root/'.work/cache';cache.mkdir(parents=True);archive.rename(cache/(digest+'.crate'))
                (root/'Cargo.lock').write_text('[[package]]\nname="crc-catalog"\nversion="0.0.1"\nsource="registry+test"\nchecksum="'+digest+'"\n')
                if mutation=='missing':(installed/'src/lib.rs').unlink()
                if mutation=='extra':(installed/'extra.rs').write_text('unexpected')
                if mutation=='changed':(installed/'src/lib.rs').write_text('changed')
                if mutation=='archive':(cache/(digest+'.crate')).write_bytes(b'wrong archive')
                data={'packages':[{'name':'crc-catalog','version':'0.0.1','source':'registry+test','manifest_path':str(installed/'Cargo.toml')}]}
                sys.path.insert(0,str(SCRIPT.parents[6]/'scripts'))
                with patch.object(adapter,'R',root),patch.object(adapter.subprocess,'check_output',return_value=json.dumps(data)):
                    if mutation=='none':adapter.catalog()
                    else:
                        with self.assertRaises((AssertionError,RuntimeError)):adapter.catalog()
