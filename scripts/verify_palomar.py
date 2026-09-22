#!/usr/bin/env python3
"""Prepare pinned verifiers and run the real Comparator with NanoDa enabled.

Run after `lake build` with the official project toolchain and ordinary pinned
checkouts. No sandbox flag is disabled. Existing exact verifier builds are reused;
a clean machine needs Git, Go 1.24.0, Rust/Cargo 1.88.0, and the pinned Lean.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--prepare-only', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
cache = Path(os.environ.get('PALOMAR_TOOLS_CACHE', str(Path.home() / '.cache/lpselfsimilar-palomar')))
assert '/tmp/' not in str(cache.resolve()), 'Use a durable verifier cache'
assert platform.system() == 'Linux', 'Landrun requires Linux'
env = os.environ.copy()
for key in ('ELAN_TOOLCHAIN', 'LEAN_PATH', 'MATHLIB_CACHE_DIR'):
    env.pop(key, None)
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, env=env, universal_newlines=True).strip())
assert '/tmp/' not in str(prefix.resolve())
certificates = [env.get('CURL_CA_BUNDLE', ''), '/etc/pki/tls/certs/ca-bundle.crt',
                '/etc/ssl/certs/ca-certificates.crt']
certificate = next(x for x in certificates if x and Path(x).is_file())
# Use Lean's bundled compiler by default; retain explicit caller overrides.
env.update(CURL_CA_BUNDLE=certificate, SSL_CERT_FILE=certificate, CARGO_HTTP_CAINFO=certificate)
local_go = Path.home() / '.local/share/lpselfsimilar-palomar/go-1.24.0/go/bin'
local_rustup = Path.home() / '.local/share/lpselfsimilar-palomar/rustup'
if local_rustup.is_dir():
    env.update(RUSTUP_HOME=str(local_rustup), CARGO_HOME=str(cache / 'cargo'))
env['PATH'] = ':'.join([str(prefix / 'bin'), str(cache / 'cargo/bin'), str(local_go), env.get('PATH','')])
env['GOPATH'] = str(cache / 'gopath')
env['GOCACHE'] = str(cache / 'go-build')
env['GOBIN'] = str(cache / 'bin')
revisions = {
    'comparator': ('https://github.com/leanprover/comparator.git', '575674928e239f5bc452aab72d1dd7b0f1326494'),
    'lean4export': ('https://github.com/leanprover/lean4export.git', '411dce7db58a3afc60ecab2d211acd1042b593dc'),
    'nanoda': ('https://github.com/robsimmons/nanoda_lib.git', '68d5ca9db226849b41a6fff59d796ff19d0a8840'),
}
landrun_revision = '811cfff51ceaf3d9843708aa6d22e9b84ccac8b4'
# The current registry Comparator pin declares rc1. Build its unchanged sources
# with the project's official rc2 compiler; record this compatibility choice.
# Its own immutable manifest remains unchanged. Other cached verifier checkouts
# remain untouched, including tools used for the author's previous projects.
def tool_path(name):
    suffix = '-' + revisions[name][1][:12] if name == 'comparator' else ''
    return cache / 'sources' / (name + suffix)
def run(command, cwd=root):
    print(f'cwd={cwd}; command={command!r}', flush=True)
    subprocess.run(command, cwd=cwd, env=env, check=True)
for name, (url, revision) in revisions.items():
    destination = tool_path(name)
    if not destination.exists():
        destination.mkdir(parents=True)
        run(['git','init',str(destination)])
        run(['git','-C',str(destination),'remote','add','origin',url])
        run(['git','-C',str(destination),'fetch','--depth','1','origin',revision])
        run(['git','-C',str(destination),'checkout','--detach',revision])
    actual = subprocess.check_output(['git','-C',str(destination),'rev-parse','HEAD'],universal_newlines=True).strip()
    assert actual == revision, (name, actual, revision)
    assert not subprocess.check_output(['git','--no-optional-locks','-C',str(destination),'diff','HEAD','--name-only'])
for name in ('comparator','lean4export'):
    tool = tool_path(name)
    if name == 'lean4export':
        assert (tool / 'lean-toolchain').read_text().strip() == (root / 'lean-toolchain').read_text().strip()
    else:
        assert (tool / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0-rc1'
        print('Building the current unchanged Comparator pin with official Lean 4.34.0-rc2.', flush=True)
    binary = tool / '.lake/build/bin' / name
    if not binary.is_file():
        run(['lake','build',name], tool)
nanoda = cache / 'sources/nanoda/target/release/nanoda_bin'
if not nanoda.is_file():
    run(['cargo','+1.88.0','build','--release','--locked'], cache / 'sources/nanoda')
landrun = cache / 'bin/landrun'
if not landrun.is_file():
    assert 'go1.24.0' in subprocess.check_output(['go','version'],env=env,universal_newlines=True)
    run(['go','install','github.com/zouuup/landrun/cmd/landrun@'+landrun_revision])
provenance = subprocess.check_output(['go','version','-m',str(landrun)],env=env,universal_newlines=True)
assert landrun_revision[:12] in provenance, provenance
binaries = {
    'comparator': tool_path('comparator') / '.lake/build/bin/comparator',
    'lean4export': cache / 'sources/lean4export/.lake/build/bin/lean4export',
    'nanoda': nanoda,
    'landrun': landrun,
}
for name, binary in binaries.items():
    assert binary.is_file() and '/tmp/' not in str(binary.resolve())
    print(name, 'SHA256', hashlib.sha256(binary.read_bytes()).hexdigest(), flush=True)
cfg = json.loads((root / 'comparator.json').read_text())
assert cfg['enable_nanoda'] is True and cfg['theorem_names']
assert len(cfg['theorem_names']) == len(set(cfg['theorem_names']))
if args.prepare_only:
    print('Exact verifier source/binary preparation passed; paper comparison not run.',flush=True)
else:
    env.update(COMPARATOR_LEAN4EXPORT=str(binaries['lean4export']),
               COMPARATOR_NANODA=str(nanoda), COMPARATOR_LANDRUN=str(landrun))
    run(['lake','env',str(binaries['comparator']),'comparator.json'])
