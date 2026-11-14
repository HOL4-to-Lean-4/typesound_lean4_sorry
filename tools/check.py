"""Checks for the sorry version.

Run from the repository root after `lake build` and `lake env lean tools/DefSorry.lean`
(which writes defsorry.tsv). Argument: path to the proved repository typesound_lean4.

1. The theorem declarations are the 269 canonical theorems of de795c9f6, plus the
   lemmas that the evaluator's termination proof needs (listed in transplant_defs.py).
2. Each canonical theorem has the baseline statement text (whitespace-insensitive)
   and the proof `sorry` and nothing else.
3. No sorry/admit outside the canonical theorems' proofs; in the kernel, the only
   declarations that mention sorryAx are the 269 canonical theorems.
4. Every definition block (def, opaque, inductive, structure, abbrev, instance) is
   textually identical to the block of the same name in typesound_lean4.
5. No axiom, native_decide, implemented_by or extern in the sources.
"""
import json
import re
import sys
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')
here = Path(__file__).resolve().parent
sys.path.insert(0, str(here))
from count_translation_progress import strip_lean_comments, DECL_RE, SORRY_RE
from transplant_defs import chunks, keyed, body, read, EVAL_SUPPORT

root = here.parent
proved = Path(sys.argv[1])
base = json.loads((here / 'baseline_theorems.json').read_text(encoding='utf-8'))
canon = {t['name']: t for t in base['theorems']}
norm = lambda s: re.sub(r'\s+', '', s)
SETOPT = re.compile(r'(?:set_option[\w.]+(?:true|false|\d+)in)+$')
problems = []

thms, sorry_total, files = [], 0, sorted((root / 'LeanTypeSound').glob('*.lean'))
for f in files:
    clean = strip_lean_comments(read(f))
    sorry_total += len(SORRY_RE.findall(clean))
    ms = list(DECL_RE.finditer(clean))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(clean)
        if m.group('kind') in ('theorem', 'lemma'):
            thms.append((f.name, m.group('name'), clean[m.start():end]))

names = [t[1] for t in thms]
extra = [n for n in names if n not in canon]
missing = [n for n in canon if n not in names]
dups = sorted({n for n in names if names.count(n) > 1})
stmt_diff, not_sorry, wrong_file = [], [], []
for f, n, content in thms:
    if n not in canon:
        continue
    st = norm(canon[n]['statement']) + ':='
    if not norm(content).startswith(st):
        stmt_diff.append(n)
        continue
    # what follows the statement: the proof, then possibly the next theorem's `set_option ... in`
    proof = SETOPT.sub('', norm(content)[len(st):])
    if proof not in ('sorry', 'bysorry'):
        not_sorry.append(n)
    if f != canon[n]['file']:
        wrong_file.append(n)
for label, lst in (('missing canonical theorems', missing), ('duplicate theorem names', dups),
                   ('statements differing from de795c9f6', stmt_diff),
                   ('canonical theorems whose proof is not exactly sorry', not_sorry),
                   ('canonical theorems in another file than in de795c9f6', wrong_file)):
    if lst:
        problems.append(f'{label}: {lst}')
if set(extra) != set(EVAL_SUPPORT):
    problems.append(f'unexpected extra theorems: {sorted(set(extra) - set(EVAL_SUPPORT))}')
if sorry_total != len(canon):
    problems.append(f'sorry/admit tokens: {sorry_total}, expected {len(canon)}')

ds = [l.split('\t') for l in (root / 'defsorry.tsv').read_text(encoding='utf-8').splitlines() if l.strip()]
ds_bad = [d for d in ds if d[1] != 'thm' or d[2].split('.')[-1] not in canon]
if ds_bad:
    problems.append(f'kernel declarations with sorryAx that are not canonical theorems: {ds_bad}')
ds_names = {d[2].split('.')[-1] for d in ds}

# definitions against typesound_lean4
def_diff, def_only_here = [], []
def_only_proved = []
prov_all, here_all = {}, {}
for p in sorted((proved / 'LeanTypeSound').glob('*.lean')):
    for k, c in keyed(chunks(read(p))):
        if k is not None:
            prov_all.setdefault(k[0], []).append((p.name, body(c)))
for f in files:
    for k, c in keyed(chunks(read(f))):
        if k is not None:
            here_all.setdefault(k[0], []).append((f.name, body(c)))
for name, lst in here_all.items():
    bodies = [b for _, b in prov_all.get(name, [])]
    for fname, b in lst:
        if not bodies:
            def_only_here.append(f'{fname}:{name}')
        elif b not in bodies:
            def_diff.append(f'{fname}:{name}')
def_only_proved = [f'{fn}:{n}' for n, lst in prov_all.items() if n not in here_all for fn, _ in lst]
proved_files = {p.name for p in (proved / 'LeanTypeSound').glob('*.lean')}
files_only_proved = sorted(proved_files - {f.name for f in files})
if def_diff or def_only_here:
    problems.append(f'definitions differing from typesound_lean4: {def_diff}; only here: {def_only_here}')

HYG = re.compile(r'_@\.[^\s()]*?_hyg\.\d+')
MATCH = re.compile(r'[^\s()]+\.match_\d+')
def types(path):
    d = {}
    for line in path.read_text(encoding='utf-8').splitlines():
        k, t = line.split('	', 1)
        d[k] = MATCH.sub('MATCH', HYG.sub('HYG', t))
    return d
type_same = type_diff = None
if (root / 'types.tsv').exists() and (proved / 'types.tsv').exists():
    ta, tb = types(root / 'types.tsv'), types(proved / 'types.tsv')
    type_same, type_diff = 0, []
    for n in canon:
        ka = [k for k in ta if k == n or k.endswith('.' + n)]
        kb = [k for k in tb if k == n or k.endswith('.' + n)]
        if len(ka) == 1 and len(kb) == 1 and ta[ka[0]] == tb[kb[0]]:
            type_same += 1
        else:
            type_diff.append(n)
    if type_diff:
        problems.append(f'kernel types differing from typesound_lean4: {type_diff}')

bad_tokens = []
for f in files:
    clean = strip_lean_comments(read(f))
    for pat in (r'(?m)^\s*axiom\s', r'\bnative_decide\b', r'\bimplemented_by\b', r'@\[extern'):
        if re.search(pat, clean):
            bad_tokens.append(f'{f.name}: {pat}')
if bad_tokens:
    problems.append(f'forbidden tokens: {bad_tokens}')

print(f'theorem declarations: {len(thms)} = {len(thms) - len(extra)} canonical + {len(extra)} '
      f'termination lemmas ({", ".join(extra)})')
print(f'canonical theorems with the de795c9f6 statement and proof exactly sorry: '
      f'{len(canon) - len(missing) - len(set(stmt_diff) | set(not_sorry))} of {len(canon)}')
print(f'sorry/admit tokens in LeanTypeSound/*.lean (comments excluded): {sorry_total}')
print(f'kernel declarations mentioning sorryAx: {len(ds)} (all canonical theorems: {not ds_bad}, '
      f'distinct names {len(ds_names)})')
print(f'definition blocks differing from typesound_lean4: {len(def_diff)}; only here: {len(def_only_here)}')
print(f'definitions of typesound_lean4 not here (proof helpers): {", ".join(def_only_proved) or "none"}')
print(f'files of typesound_lean4 left out: {", ".join(files_only_proved)}')
if type_same is not None:
    print(f'kernel types equal to typesound_lean4 (hygiene and matcher names normalised): {type_same} of {len(canon)}')
print(f'axiom/native_decide/implemented_by/extern: {len(bad_tokens)}')
print(f'problems: {len(problems)}')
for p in problems:
    print('  ' + p)
sys.exit(1 if problems else 0)
