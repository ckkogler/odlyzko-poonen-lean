#!/usr/bin/env python3
"""Audit an actual full-paper Verification.lean run; do not replace semantic review."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('result', type=Path, help='actual saved command basename, without .log')
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
base = args.result.resolve()
assert base.with_suffix('.exit').read_text().strip() == '0'
output = base.with_suffix('.log').read_text()
source = (root / 'Verification.lean').read_text()
expected = re.findall(r'^#print axioms (\S+)', source, re.M)
actual = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
assert len(actual) == len(expected), (len(actual),len(expected))
assert [name for name,_ in actual] == expected
for name, axioms in actual:
    assert {x.strip() for x in axioms.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}, (name,axioms)
snapshot=json.loads(base.with_suffix('.sources.json').read_text())
assert snapshot==json.loads(base.with_suffix('.sources-after.json').read_text())
for relative,digest in snapshot.items():
    assert hashlib.sha256((root/relative).read_bytes()).hexdigest()==digest, relative
source_names=[]
for p in sorted((root/'OdlyzkoPoonen').rglob('*.lean')):
    source_names.extend('OdlyzkoPoonen.'+n for n in re.findall(r'^(?:lemma|theorem)\s+(\S+)',p.read_text(),re.M))
assert source_names==expected and len(set(expected))==len(expected)==672
claims = json.loads((root / 'comparator.json').read_text())['theorem_names']
for name in claims:
    assert name in expected and 'theorem '+name in output, name
assert 'sorryAx' not in output and 'Lean.ofReduceBool' not in output
sha = hashlib.sha256(output.encode()).hexdigest()
print(f'Actual full Verification.lean exit 0: {len(actual)} standard-only axiom lists, {len(claims)} configured statements present.')
print(f'Output SHA256 {sha}')
print('Full statement meanings, constants and hypothesis audits are documented separately; this is not human review.')
receipt = dict(finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               actual_exit=0,axiom_lists=len(actual),main_theorems=claims,
               output_sha256=sha,verification_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
               scope='Actual exit/output and permitted-axiom audit. Separate full semantic review is required.')
base.with_suffix('.audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
