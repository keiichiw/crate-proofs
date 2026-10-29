"""Checked relocation of file-name metadata; executable LLBC is unchanged."""
from pathlib import Path
import copy, hashlib, json

def canonicalize(path, crate, cwd):
    path=Path(path);crate=Path(crate);cwd=Path(cwd)
    raw=path.read_bytes();original=json.loads(raw)
    assert original['has_errors'] is False
    changed=copy.deepcopy(original);rows=[]
    lock=json.loads((crate/'source.lock.json').read_text())
    for index,record in enumerate(changed['translated']['files']):
        if record is None or record['crate_name']!='crc':continue
        assert set(record['name'])=={'Local'},record['name']
        value=record['name']['Local'];actual=Path(value)
        actual=actual if actual.is_absolute() else cwd/actual
        relative=actual.resolve().relative_to((crate/'upstream').resolve()).as_posix()
        assert relative in lock['files'],relative
        data=actual.read_bytes()
        assert hashlib.sha256(data).hexdigest()==lock['files'][relative]['sha256']
        if record['contents'] is not None:assert record['contents'].encode()==data
        canonical='crc-source/'+relative
        rows.append({'index':index,'old':value,'new':canonical,'source_sha256':lock['files'][relative]['sha256']})
        record['name']['Local']=canonical
    assert rows,'No original crc source coordinates found'
    restored=copy.deepcopy(changed)
    for row in rows:
        assert original['translated']['files'][row['index']]['name']=={'Local':row['old']}
        restored['translated']['files'][row['index']]['name']={'Local':row['old']}
    assert restored==original,'Change outside exact reviewed source filename metadata'
    raw_path=path.with_suffix('.raw.llbc');raw_path.write_bytes(raw)
    path.write_text(json.dumps(changed,separators=(',',':'))+'\n')
    path.with_suffix('.source-coordinates.json').write_text(json.dumps({'kind':'source-file-name-only relocation; no executable/type/span/content changes','original_sha256':hashlib.sha256(raw).hexdigest(),'relocated_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'files':rows},indent=2)+'\n')
