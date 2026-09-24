#!/usr/bin/env python3
"""Run one final check with the durable official pinned Lean environment.

Each invocation saves its real output, timestamps, command, and exit status in a
new full-paper audit directory, preserving all historical completion evidence.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
label, *command = sys.argv[1:]
log_dir = Path(os.environ.get('ODLYZKO_VERIFICATION_LOG_DIR', str(root / 'logs/verification')))
base = log_dir / label
base.parent.mkdir(parents=True, exist_ok=True)
assert not base.with_suffix('.started').exists(), f'Preserve existing run: {label}'
prefix = Path.home() / '.elan/toolchains/leanprover--lean4---v4.35.0-rc2'
assert prefix.is_dir() and '/tmp/' not in str(prefix.resolve())
env = os.environ.copy()
for name in ('ELAN_TOOLCHAIN', 'LEAN_PATH', 'MATHLIB_CACHE_DIR'):
    env.pop(name, None)
certificate = next(p for p in (env.get('CURL_CA_BUNDLE', ''),
    '/etc/pki/tls/certs/ca-bundle.crt', '/etc/ssl/certs/ca-certificates.crt')
    if p and Path(p).is_file())
# Use Lean's bundled compiler by default; retain explicit caller overrides.
env.update(CURL_CA_BUNDLE=certificate, LEAN_NUM_THREADS='4')
env['PATH'] = str(prefix / 'bin') + ':' + str(Path.home() / '.elan/bin') + ':' + env.get('PATH', '')
def snapshot():
    paths=list((root/'OdlyzkoPoonen').rglob('*.lean'))
    paths += [root/name for name in ['OdlyzkoPoonen.lean','Verification.lean','Challenge.lean',
        'Solution.lean','comparator.json','lean-toolchain','lakefile.toml','lake-manifest.json']]
    return {p.relative_to(root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}
before=snapshot()
base.with_suffix('.sources.json').write_text(json.dumps(before,indent=2)+'\n')
actual_version=subprocess.check_output([str(prefix/'bin/lean'),'--version'],cwd=root,env=env,universal_newlines=True).strip()
assert '4.35.0-rc2' in actual_version and '11acb17ec6b07a8f9e9173e6845197929540936b' in actual_version, actual_version
base.with_suffix('.environment.json').write_text(json.dumps(dict(
    toolchain_prefix=str(prefix),version=actual_version,
    settings={k:env.get(k) for k in ['LEAN_CC','LIBRARY_PATH','LEAN_NUM_THREADS','CURL_CA_BUNDLE','ELAN_TOOLCHAIN','LEAN_PATH','MATHLIB_CACHE_DIR']}
),indent=2)+'\n')
base.with_suffix('.command').write_text(repr(command) + '\n')
base.with_suffix('.started').write_text(datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n')
with base.with_suffix('.log').open('w') as out:
    result = subprocess.run(command, cwd=root, env=env, stdout=out, stderr=subprocess.STDOUT)
after=snapshot()
base.with_suffix('.sources-after.json').write_text(json.dumps(after,indent=2)+'\n')
base.with_suffix('.exit').write_text(str(result.returncode) + '\n')
base.with_suffix('.finished').write_text(datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n')
print(f'{label}: actual exit {result.returncode}; output {base.with_suffix(".log")}', flush=True)
assert before==after, 'Source changed during verification; inspect and rerun'
sys.exit(result.returncode)
