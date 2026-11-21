"""Verify a workspace against the all-sorry baseline.

Usage: python3 verify.py <workspace> [--no-build]
Run from anywhere. Needs lake on PATH. Writes <workspace>/verify_report.txt and prints it.

A canonical theorem counts as PROVED when
  - its source statement text equals the baseline statement (whitespace-insensitive),
  - its kernel type equals the baseline kernel type,
  - its axioms are a subset of {propext, Classical.choice, Quot.sound} (so no sorryAx).
Also checked: every baseline definition/constant is unchanged in the kernel, no new
axiom / native_decide / implemented_by / extern / unsafe tokens, build succeeds.
"""
import json, re, subprocess, sys, os, time
from pathlib import Path
here = Path(__file__).resolve().parent
sys.path.insert(0, str(here))
from count_translation_progress import strip_lean_comments, DECL_RE
ws = Path(sys.argv[1]).resolve()
env = dict(os.environ); env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env['PATH']
canon = {t['name']: t for t in json.loads((here / 'baseline_theorems.json').read_text())['theorems']}
norm = lambda s: re.sub(r'\s+', '', s)
OK_AX = {'propext', 'Classical.choice', 'Quot.sound'}
out = []
build_ok = True
if '--no-build' not in sys.argv:
    r = subprocess.run(['lake', 'build'], cwd=ws, env=env, capture_output=True, text=True)
    build_ok = r.returncode == 0
    (ws / 'verify_build.log').write_text(r.stdout + r.stderr)
    if not build_ok:
        errs = [l for l in (r.stdout + r.stderr).splitlines() if 'error' in l][:20]
        out.append('BUILD FAILED:\n  ' + '\n  '.join(errs))
r = subprocess.run(['lake', 'env', 'lean', str(here / 'Audit.lean')], cwd=ws, env=env, capture_output=True, text=True)
if r.returncode != 0:
    out.append('AUDIT FAILED: ' + (r.stdout + r.stderr)[:2000])
    print('\n'.join(out)); sys.exit(2)
HYG = re.compile(r'_@\.[^\s()]*?_hyg\.\d+'); MATCH = re.compile(r'[^\s()]+\.match_\d+')
def thms(p):
    d = {}
    for line in p.read_text().splitlines():
        n, mod, ax, direct, ty = line.split('\t', 4)
        d[n.split('.')[-1] if n.split('.')[-1] in canon and n.split('.')[-1] not in d else n] = (mod, set(a for a in ax.split(',') if a), MATCH.sub('MATCH', HYG.sub('HYG', ty)), direct == 'true')
    return d
def defs(p):
    return {l.split('\t')[0]: l.split('\t')[1:] for l in p.read_text().splitlines() if l.strip()}
cur_t, cur_d = thms(ws / 'audit_thms.tsv'), defs(ws / 'audit_defs.tsv')
base_t, base_d = thms(here / 'base_thms.tsv'), defs(here / 'base_defs.tsv')
# source statements
src = {}
bad_tokens = []
for f in sorted((ws / 'LeanTypeSound').glob('*.lean')):
    clean = strip_lean_comments(f.read_text())
    for pat in (r'(?m)^\s*(private\s+|protected\s+)?axiom\s', r'\bnative_decide\b', r'\bimplemented_by\b', r'@\[extern', r'\bunsafe\b', r'\bofReduceBool\b', r'\bdebug\.skipKernelTC\b'):
        if re.search(pat, clean): bad_tokens.append(f'{f.name}: {pat}')
    ms = list(DECL_RE.finditer(clean))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(clean)
        if m.group('kind') in ('theorem', 'lemma') and m.group('name') in canon:
            src.setdefault(m.group('name'), []).append((f.name, clean[m.start():end]))
direct_free, proved, unproved, stmt_changed, type_changed, moved, missing, bad_ax = [], [], [], [], [], [], [], []
for n, t in canon.items():
    if n not in src or n not in cur_t: missing.append(n); continue
    fname, content = src[n][0]
    if len(src[n]) > 1 or not norm(content).startswith(norm(t['statement']) + ':='): stmt_changed.append(n); continue
    if fname != t['file']: moved.append(n)
    if cur_t[n][2] != base_t[n][2]: type_changed.append(n); continue
    ax = cur_t[n][1]
    if not cur_t[n][3]: direct_free.append(n)
    if 'sorryAx' in ax: unproved.append(n)
    elif ax - OK_AX: bad_ax.append((n, sorted(ax - OK_AX)))
    else: proved.append(n)
def_changed = [n for n, v in base_d.items() if cur_d.get(n) != v]
new_axioms = [n for n, v in cur_d.items() if v[1] == 'axiom']
out.append(f'time: {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}')
out.append(f'build ok: {build_ok}')
out.append(f'PROVED: {len(proved)} of {len(canon)}')
out.append(f'own proof has no sorry (dependencies may still have): {len(direct_free)} of {len(canon)}')
out.append(f'still sorry (directly or through a sorry dependency): {len(unproved)}')
out.append(f'statement text changed: {stmt_changed}')
out.append(f'kernel type changed: {type_changed}')
out.append(f'missing: {missing}')
out.append(f'moved to another file: {moved}')
out.append(f'non-standard axioms: {bad_ax}')
out.append(f'baseline definitions changed in kernel: {def_changed[:40]} ({len(def_changed)})')
out.append(f'axiom declarations: {new_axioms}')
out.append(f'forbidden tokens: {bad_tokens}')
by_file = {}
for n in canon:
    by_file.setdefault(canon[n]['file'], [0, 0, 0]); by_file[canon[n]['file']][1] += 1
    if n in proved: by_file[canon[n]['file']][0] += 1
    if n in direct_free: by_file[canon[n]['file']][2] += 1
out.append('per file (fully proved / total; own proof sorry-free): ' + ', '.join(f'{f} {a}/{b} ({c})' for f, (a, b, c) in sorted(by_file.items())))
out.append('own proof still sorry: ' + ' '.join(sorted(set(canon) - set(direct_free))))
out.append('unproved: ' + ' '.join(sorted(unproved)))
(ws / 'verify_report.txt').write_text('\n'.join(out) + '\n')
(ws / 'verify_proved.txt').write_text('\n'.join(sorted(proved)) + '\n')
print('\n'.join(out))
