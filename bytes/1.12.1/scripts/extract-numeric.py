"""Extract the four safe byte readers using the separately pinned stage2 tool."""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess
parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--aeneas', type=Path, required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
run = args.output.resolve()
run.mkdir(parents=True, exist_ok=False)
binary = args.aeneas.resolve(strict=True)
script = Path(__file__).resolve()
script_bytes = script.read_bytes()
harness = root/'tests/numeric'
inputs = [harness/'Cargo.toml',harness/'Cargo.lock',harness/'src/lib.rs',
          root/'.work/source/src/buf/buf_impl.rs',root/'scripts/extract-numeric.sh']
input_bytes = {path:path.read_bytes() for path in inputs}
def sha256(data):
    return hashlib.sha256(data).hexdigest()

entries = ['read_i8','try_read_i8','read_u8','try_read_u8','force_slice_dictionary']
includes = ['bytes::buf::buf_impl::_','bytes::buf::take','bytes::panic_advance','bytes::TryGetError']
includes += ['bytes::buf::buf_impl::Buf::'+name for name in
             ['get_i8','try_get_i8','get_u8','try_get_u8','has_remaining']]
charon = ['charon','cargo','--preset=aeneas','--duplicate-defaulted-methods',
          '--remove-unused-self-clauses','--opaque','bytes','--opaque','bytes::buf::buf_impl::Buf']
charon += [arg for name in includes for arg in ['--include',name]]
charon += [arg for name in entries for arg in ['--start-from','crate::'+name]]
charon += ['--dest-file',str(run/'bytes_numeric.llbc'),'--','--lib','--locked']
aeneas = [str(binary),'-backend','lean','-filter-trait-methods','-rooted-declarations',
          '-normalize-shared-reborrow','-order-projected-declarations',
          '-dest',str(run),str(run/'bytes_numeric.llbc')]
env = dict(os.environ, CARGO_TARGET_DIR=str(run/'target'))
records = []
for name,command in [('charon',charon),('aeneas',aeneas)]:
    executable = Path(shutil.which(command[0])).resolve()
    with (run/f'{name}.log').open('w') as log:
        out = subprocess.run(command,cwd=root/'tests/numeric',env=env,
                             stdout=log,stderr=subprocess.STDOUT)
    if not executable.is_file():
        raise SystemExit(f'Missing executable: {executable}')
    records.append({'stage':name,'command':command,'exit_code':out.returncode,
                    'executable':str(executable),'sha256':hashlib.sha256(executable.read_bytes()).hexdigest()})
    (run/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
    if out.returncode:
        raise SystemExit(out.returncode)
actual_models = {str(path.relative_to(run)) for path in run.rglob('*.lean')}
expected_models = {'BytesNumeric.lean'}
if actual_models != expected_models:
    raise SystemExit(f'Numeric model inventory mismatch: {actual_models} != {expected_models}')
model = run/'BytesNumeric.lean'
text = model.read_text()
if re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',text):
    raise SystemExit('Rejected numeric extraction: incomplete or unsupported generated declaration')
if re.search(r'partial\s+file', (run/'aeneas.log').read_text(), re.IGNORECASE):
    raise SystemExit('Rejected partial numeric extraction')
required = ['Shared0SliceU8.Insts.BytesBufBuf_implBuf.'+method for method in
            ['get_u8','try_get_u8','get_i8','try_get_i8']]
for name in required:
    declarations = list(re.finditer(rf'(?m)^\s*def\s+{re.escape(name)}(?=\s|\(|:)',text))
    if len(declarations) != 1:
        raise SystemExit(f'Expected exactly one actual reader declaration: {name}')
    start = declarations[0].start()
    comment_start = text.rfind('/--',0,start)
    comment = text[comment_start:start] if comment_start >= 0 else ''
    expected_source = "Source: '"+str(Path('/crate/bytes/1.12.1')/'.work/source/src/buf/buf_impl.rs')+"'"
    if expected_source not in comment or '::'+name.rsplit('.',1)[1]+']' not in comment:
        raise SystemExit(f'Wrong or absent upstream reader provenance: {name}')
if script.read_bytes() != script_bytes or any(path.read_bytes() != raw for path,raw in input_bytes.items()):
    raise SystemExit('Numeric extraction inputs changed during execution')
command_file = run/'commands.json'
result = {
    'status':'extracted-not-proved',
    'commands':records,
    'command_sha256':sha256(command_file.read_bytes()),
    'script_sha256':sha256(script_bytes),
    'inputs_sha256':{str(path.relative_to(root)):sha256(raw) for path,raw in input_bytes.items()},
    'models_sha256':{'BytesNumeric.lean':sha256(model.read_bytes())},
    'required_definitions':required,
    'files_sha256':{name:sha256((run/name).read_bytes()) for name in
                    ['commands.json','charon.log','aeneas.log','bytes_numeric.llbc','BytesNumeric.lean']},
}
(run/'extraction.json').write_text(json.dumps(result,indent=2)+'\n')
print(f'Extracted (not proved): {model}')
