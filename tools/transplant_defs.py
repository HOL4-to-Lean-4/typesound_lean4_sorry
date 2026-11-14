"""Bring the corrected definitions of typesound_lean4 into the frozen translation.

The frozen translation de795c9f6 (in LeanTypeSound/) has the 269 theorems with
`sorry` proofs. This script replaces, file by file, every top-level definition
block (def, opaque, inductive, structure, abbrev, instance) whose text differs in
typesound_lean4 by the typesound_lean4 block, takes typesound_lean4's prelude as a
whole (it has no theorems), and inserts the lemmas that the evaluator's
termination proof uses. Theorem blocks are not touched.

Usage: python tools/transplant_defs.py <path to typesound_lean4>
"""
import re
import sys
from pathlib import Path

START = re.compile(r'(?:/-|--|@\[|def |theorem |lemma |inductive |structure |abbrev |instance |'
                   r'mutual\b|end\b|namespace |open |set_option |noncomputable |partial |private |'
                   r'protected |unsafe |opaque |section|variable |attribute |class |macro|syntax|elab|#)')
HEAD = re.compile(r'(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*'
                  r'(def|opaque|inductive|structure|abbrev|instance|theorem|lemma)\s+([^\s(:={\[]+)')
DEFKINDS = {'def', 'opaque', 'inductive', 'structure', 'abbrev', 'instance'}
# Lemmas used by the termination proof of evaluate / evaluate_match / evaluate_decs.
EVAL_SUPPORT = ['fix_clock_clock_le', 'lex_le_lt', 'lex_lt', 'do_log_exp', 'do_if_exp',
                'list_sizeOf_append', 'list_sizeOf_reverse', 'pat_sizeOf_pos', 'list_sizeOf_pos']


def read(p):
    return p.read_text(encoding='utf-8').replace('\r\n', '\n')


def chunks(text):
    """Split into top-level chunks; each starts at a column-0 command or comment line."""
    lines = text.split('\n')
    out, cur = [], []
    for ln in lines:
        if ln and not ln[0].isspace() and START.match(ln) and cur:
            out.append('\n'.join(cur))
            cur = []
        cur.append(ln)
    out.append('\n'.join(cur))
    return out


def keyed(cs):
    occ, res = {}, []
    for c in cs:
        m = HEAD.match(c)
        if m and m.group(1) in DEFKINDS:
            name = m.group(2)
            k = occ.get(name, 0)
            occ[name] = k + 1
            res.append(((name, k), c))
        else:
            res.append((None, c))
    return res


def body(c):
    # a definition chunk without trailing blank lines
    return c.rstrip('\n ')


def main():
    src = Path(sys.argv[1]) / 'LeanTypeSound'
    dst = Path(__file__).resolve().parent.parent / 'LeanTypeSound'
    report = []
    for f in sorted(dst.glob('*.lean')):
        s = src / f.name
        if f.name == 'HOL4Prelude.lean':
            f.write_text(read(s).replace('\n', '\r\n'), encoding='utf-8', newline='')
            report.append(f'{f.name}: taken whole from typesound_lean4')
            continue
        base = keyed(chunks(read(f)))
        new = dict(k for k in keyed(chunks(read(s))) if k[0] is not None)
        support = {}
        if f.name == 'Evaluate.lean':
            for c in chunks(read(s)):
                m = HEAD.match(c)
                if m and m.group(2) in EVAL_SUPPORT:
                    support[m.group(2)] = c
        out, changed = [], []
        for key, c in base:
            if f.name == 'Evaluate.lean' and c.startswith('mutual') and support:
                for n in EVAL_SUPPORT:
                    out.append(support[n])
                report.append(f'{f.name}: inserted termination lemmas {", ".join(EVAL_SUPPORT)}')
                support = {}
            if key is not None and key in new and body(new[key]) != body(c):
                trail = c[len(body(c)):]
                out.append(body(new[key]) + trail)
                changed.append(key[0] + (f'#{key[1]}' if key[1] else ''))
            else:
                out.append(c)
        if changed:
            report.append(f'{f.name}: replaced {", ".join(changed)}')
        f.write_text('\n'.join(out).replace('\n', '\r\n'), encoding='utf-8', newline='')
    print('\n'.join(report))


if __name__ == '__main__':
    main()
