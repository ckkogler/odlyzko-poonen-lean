#!/usr/bin/env python3
"""Run licensee 10.0.0 and require the same single SPDX identifier as the metadata."""
from pathlib import Path
import json
import os
import subprocess

root = Path(__file__).resolve().parent.parent
env = os.environ.copy()
ruby = Path.home() / '.local/share/lpselfsimilar-palomar/ruby-3.3.12/bin'
if ruby.is_dir():
    env['PATH'] = str(ruby) + ':' + env.get('PATH', '')
    env['BUNDLE_PATH'] = str(Path.home() / '.cache/lpselfsimilar-palomar/ruby-gems')
env['BUNDLE_FORCE_RUBY_PLATFORM'] = 'true'
env['BUNDLE_FROZEN'] = 'true'
result = subprocess.run(['bundle', 'exec', 'licensee', 'detect', 'LICENSE', '--json',
                         '--no-packages', '--no-readme'], cwd=root, env=env,
                        universal_newlines=True, stdout=subprocess.PIPE, check=True)
report = json.loads(result.stdout)
print(json.dumps(report, indent=2), flush=True)
identifiers = [item['spdx_id'] for item in report['licenses']]
assert identifiers == ['0BSD'], identifiers
assert '  license: 0BSD' in (root / 'formalization.yaml').read_text()
print('Actual licensee 10.0.0 detection: exactly 0BSD, matching formalization.yaml.', flush=True)
