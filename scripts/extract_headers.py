#!/usr/bin/env python3
"""Extract a short file-level description from the top comment/docstring of each .lean file."""
import os, re, json

ROOT = os.path.join(os.path.dirname(__file__), '..')
RGF = os.path.join(ROOT, 'RGF')

def header(path):
    with open(path, encoding='utf-8') as f:
        txt = f.read()
    # find first block comment /-! ... -/ or /-- ... -/ or /- ... -/
    m = re.search(r'/-[!-]?(.*?)-/', txt, re.S)
    if m:
        body = m.group(1)
        # strip markdown headers markers and copyright lines
        lines = [l.strip() for l in body.splitlines()]
        lines = [l for l in lines if l and not l.startswith('Copyright') and not l.startswith('Released') and not l.startswith('Authors') and not l.lower().startswith('import')]
        text = ' '.join(lines)
        text = re.sub(r'[#*`]+', '', text)
        text = ' '.join(text.split())
        return text[:600]
    return ''

result = {}
for dirpath, dirs, files in os.walk(RGF):
    for fn in sorted(files):
        if fn.endswith('.lean'):
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, ROOT)
            result[rel] = header(full)

with open(os.path.join(ROOT, 'scripts', 'headers.json'), 'w', encoding='utf-8') as f:
    json.dump(result, f, ensure_ascii=False, indent=1)
print('done', len(result))
