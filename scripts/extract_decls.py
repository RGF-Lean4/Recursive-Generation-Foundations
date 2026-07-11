#!/usr/bin/env python3
"""Extract all theorem/lemma declarations (name + signature + docstring) from RGF .lean files."""
import os, re, json

ROOT = os.path.join(os.path.dirname(__file__), '..')
RGF = os.path.join(ROOT, 'RGF')

DECL_RE = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma)\s+([^\s:({\[]+)')

def compute_in_comment(lines):
    """Return list of booleans: True if the line STARTS inside a block comment."""
    flags = []
    depth = 0
    for line in lines:
        flags.append(depth > 0)
        p = 0
        s = line
        while p < len(s) - 1:
            two = s[p:p+2]
            if two == '/-':
                depth += 1
                p += 2
                continue
            if two == '-/':
                if depth > 0:
                    depth -= 1
                p += 2
                continue
            if two == '--' and depth == 0:
                break
            p += 1
    return flags

def extract_file(path):
    with open(path, encoding='utf-8') as f:
        lines = f.readlines()
    in_comment = compute_in_comment(lines)
    decls = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = DECL_RE.match(line)
        if m and not in_comment[i]:
            kind = m.group(1)
            name = m.group(2)
            # capture docstring: look backwards for /-- ... -/ ending on previous non-attr line
            doc = ''
            j = i - 1
            # skip attribute lines directly above
            while j >= 0 and re.match(r'^\s*@\[', lines[j]):
                j -= 1
            if j >= 0 and lines[j].rstrip().endswith('-/'):
                # find start
                k = j
                buf = []
                while k >= 0:
                    buf.append(lines[k])
                    if '/--' in lines[k]:
                        break
                    k -= 1
                buf.reverse()
                doctext = ''.join(buf)
                dm = re.search(r'/--(.*?)-/', doctext, re.S)
                if dm:
                    doc = ' '.join(dm.group(1).split())
            # capture signature from decl start until top-level ':='
            sig_lines = []
            depth = 0
            found = False
            for k in range(i, min(i + 40, n)):
                cur = lines[k]
                # search char by char for := at depth 0
                idx = 0
                seg = cur
                # track brackets
                stop_col = None
                bd = depth
                p = 0
                while p < len(seg):
                    c = seg[p]
                    if c in '([{':
                        bd += 1
                    elif c in ')]}':
                        bd -= 1
                    elif c == ':' and p + 1 < len(seg) and seg[p+1] == '=' and bd == 0:
                        stop_col = p
                        break
                    p += 1
                if stop_col is not None:
                    sig_lines.append(seg[:stop_col])
                    found = True
                    break
                else:
                    sig_lines.append(seg.rstrip('\n'))
                    depth = bd
            sig = ' '.join(' '.join(sig_lines).split())
            decls.append({'kind': kind, 'name': name, 'sig': sig, 'doc': doc})
            i = i + 1
        else:
            i += 1
    return decls

result = {}
for dirpath, dirs, files in os.walk(RGF):
    for fn in sorted(files):
        if fn.endswith('.lean'):
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, ROOT)
            result[rel] = extract_file(full)

with open(os.path.join(ROOT, 'scripts', 'decls.json'), 'w', encoding='utf-8') as f:
    json.dump(result, f, ensure_ascii=False, indent=1)

total = sum(len(v) for v in result.values())
print('files:', len(result), 'decls:', total)
