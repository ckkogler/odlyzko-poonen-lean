#!/usr/bin/env python3
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--prepare-only', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
assert platform.system() == 'Linux'
assert (root / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
env = os.environ.copy()
for key in ('ELAN_TOOLCHAIN', 'LEAN_PATH', 'MATHLIB_CACHE_DIR'):
    env.pop(key, None)
prefix = Path(subprocess.check_output(
    ['lean', '--print-prefix'], cwd=root, env=env, text=True).strip())
version = subprocess.check_output([str(prefix / 'bin/lean'), '--version'], text=True)
assert '4.35.0-rc2' in version and '11acb17ec6b07a8f9e9173e6845197929540936b' in version, version
env['PATH'] = str(prefix / 'bin') + os.pathsep + env.get('PATH', '')
binaries = {name: prefix / 'bin' / name for name in
            ('lake', 'lean', 'leanexport', 'leanchecker', 'nanoda_bin', 'con-ron')}
for name, binary in binaries.items():
    assert binary.is_file() and os.access(binary, os.X_OK), name
    print(name, 'SHA256', hashlib.sha256(binary.read_bytes()).hexdigest(), flush=True)
bwrap = shutil.which(env.get('COMPARATOR_BWRAP', 'bwrap'), path=env['PATH'])
assert bwrap, 'Install bubblewrap 0.12.0 and set COMPARATOR_BWRAP to its executable.'
bwrap_version = subprocess.check_output([bwrap, '--version'], text=True).strip()
assert bwrap_version == 'bubblewrap 0.12.0', bwrap_version
env['COMPARATOR_BWRAP'] = bwrap
print('bubblewrap SHA256', hashlib.sha256(Path(bwrap).read_bytes()).hexdigest(), flush=True)
cfg = json.loads((root / 'comparator.json').read_text())
assert cfg.pop('enable_nanoda', False) is True
assert cfg['theorem_names'] and len(cfg['theorem_names']) == len(set(cfg['theorem_names']))
assert set(cfg['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
cfg['external_kernels'] = {
    'nanoda': [str(binaries['nanoda_bin'])],
    'con-ron': [str(binaries['con-ron'])],
}
destination = root / '.lake/palomar-comparator.json'
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(json.dumps(cfg, indent=2) + '\n')
if args.prepare_only:
    print('Bundled verifier preparation passed; comparison not run.', flush=True)
else:
    command = [str(binaries['lake']), 'comparator', '--config', str(destination)]
    print('command:', command, flush=True)
    subprocess.run(command, cwd=root, env=env, check=True)
