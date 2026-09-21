#!/usr/bin/env python3
"""Validate the contained metadata and isolated statement surface.

This structural audit supplements the actual Comparator and semantic inspection.
It never treats a count or a matching hash as an independent proof check.
"""
from pathlib import Path
import hashlib,json,re,os
import yaml,jsonschema
from lean_source_text import code_text
root=Path(__file__).resolve().parent.parent
class UniqueLoader(yaml.SafeLoader):
    pass
def mapping(loader,node,deep=False):
    out={}
    for key,value in node.value:
        k=loader.construct_object(key,deep=deep)
        assert k not in out and k!='<<', ('duplicate/merge YAML key',k)
        out[k]=loader.construct_object(value,deep=deep)
    return out
UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,mapping)
metadata=yaml.load((root/'formalization.yaml').read_text(),Loader=UniqueLoader)
schema=json.loads((root/'reference/palomar/schema/v0.4.schema.json').read_text())
jsonschema.Draft7Validator(schema).validate(metadata)
assert metadata['version']=='v0.4'
assert metadata['project']['authors']==['Constantin Kogler']
assert metadata['project']['responsible_maintainers']==['Constantin Kogler']
assert metadata['project']['license']=='0BSD'
assert 0<len(metadata['project']['description'])<=10000
assert metadata['status']['sorry_count']==metadata['status']['sorry_in_definitions']==0
standard={'propext','Quot.sound','Classical.choice'}
assert set(metadata['status']['axioms'])<=standard
assert metadata['classification']['arxiv']==['math.NT','math.PR']
assert metadata['classification']['msc2020']==['11C08','60C05']
assert 'repository' not in metadata, 'This is the substantive development'
assert all(s['relationship'] in {'formalizes','adapts','independently-proves','background','other'} for s in metadata['sources'])
assert all(s.get('type','paper') in {'paper','book','web discussion','folklore','other'} for s in metadata['sources'])
assert any(s['relationship']=='formalizes' for s in metadata['sources'])
assert metadata['sources'][0]['authors']==['Constantin Kogler']
assert hashlib.sha256((root/'LICENSE').read_bytes()).hexdigest()=='91f30b27b3723ccdda0f91a1eeef974e61dda88b2ca145e25e5c5320d69574ac'
cfg=json.loads((root/'comparator.json').read_text())
assert set(cfg)=={'challenge_module','solution_module','theorem_names','definition_names','permitted_axioms','enable_nanoda'}
assert cfg['challenge_module']=='Challenge' and cfg['solution_module']=='Solution'
assert cfg['definition_names']==[] and cfg['enable_nanoda'] is True
assert set(cfg['permitted_axioms'])==standard
claim_count=len(cfg['theorem_names'])
assert claim_count>0 and claim_count==len(set(cfg['theorem_names']))
challenge=root/'Challenge.lean';text=challenge.read_text();code=code_text(text)
assert not challenge.is_symlink() and len(text.encode())<=100*1024 and len(text.splitlines())<=1000
imports=re.findall(r'^import (\S+)',code,re.M)
assert imports and all(i.startswith('Mathlib.') for i in imports)
assert len(re.findall(r'\bsorry\b',code))==claim_count
assert not re.search(r'\b(admit|axiom|native_decide|unsafe|implemented_by|skipKernelTC|trustLevel)\b',code)
challenge_names=['OdlyzkoPoonen.'+n for n in re.findall(r'^(?:lemma|theorem)\s+(\S+)',code,re.M)]
assert challenge_names==cfg['theorem_names']
seen=set()
def visit(module):
    if module in seen:return
    assert module!='Challenge', 'Challenge entered proved closure'
    seen.add(module)
    p=root/(module.replace('.','/')+'.lean')
    if not p.is_file():return
    assert not p.is_symlink()
    c=code_text(p.read_text())
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|skipKernelTC|trustLevel)\b',c),p
    for name in re.findall(r'^import (\S+)',c,re.M):
        if (root/(name.replace('.','/')+'.lean')).is_file():visit(name)
visit('Solution')
expected_modules={str(p.relative_to(root).with_suffix('')).replace('/','.')
                  for p in (root/'OdlyzkoPoonen').rglob('*.lean')}
assert seen==expected_modules|{'OdlyzkoPoonen','Solution'}
assert set(cfg['theorem_names'])<={x['lean'] for x in metadata['alignment']['statements']}
assert set(cfg['theorem_names'])<=set(re.findall(r'^#print axioms (\S+)',(root/'Verification.lean').read_text(),re.M))
for pkg in json.loads((root/'lake-manifest.json').read_text())['packages']:
    assert pkg['type']=='git' and re.fullmatch('[0-9a-f]{40}',pkg['rev'])
    assert re.fullmatch(r'https://github.com/[^/?#]+/[^/?#]+(?:\.git)?',pkg['url'])
for rel,digest in json.loads((root/'verification/proof-source-baseline.json').read_text())['sources'].items():
    assert hashlib.sha256((root/rel).read_bytes()).hexdigest()==digest,rel
for e in json.loads((root/'provenance/reused-source.json').read_text())['files']:
    assert hashlib.sha256((root/e['destination']).read_bytes()).hexdigest()==e['destination_sha256']
assert (root/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.0-rc2'
mathlib_toolchain=root/'.lake/packages/mathlib/lean-toolchain'
assert mathlib_toolchain.is_file(), 'Resolve the pinned Mathlib dependency before validation'
assert mathlib_toolchain.read_text().strip()==(root/'lean-toolchain').read_text().strip(), 'Project and pinned Mathlib toolchains must match exactly'
assert not (root/'lakefile.lean').exists()
print('Metadata: v0.4 schema, attribution, source relationships, classification and license passed.')
print(f'Challenge: {len(text.splitlines())} lines, {len(text.encode())} bytes; {claim_count} independent claims, no definition holes.')
print(f'Solution: all {len(expected_modules)} proof modules, default root and Solution; no Challenge import or unchecked shortcut.')
print(f'All {claim_count} claims aligned and covered by full Verification.lean; exact public Git pins, matching Mathlib toolchain and contained reuse.')
print('This structural validation does not replace kernel checking, full semantic review or registry review.')
