import json,re,os,sys
sys.path.insert(0,'/home/claude/work/benchtools')
from count_translation_progress import strip_lean_comments, DECL_RE
canon=[t for t in json.load(open('tools/baseline_theorems.json'))['theorems']]
# HOL4 theorems
hol={}
for f in os.listdir('hol4-ultramin'):
    if not f.endswith('.sml'): continue
    s=open('hol4-ultramin/'+f,encoding='utf-8',errors='replace').read()
    for m in re.finditer(r'(?m)^(Theorem|Triviality)\s+([A-Za-z0-9_\']+)(\[[^\]]*\])?\s*:(.*?)^Proof(.*?)^QED',s,re.S):
        hol.setdefault(m.group(2),(f,m.group(4).strip(),m.group(5).strip()))
    for m in re.finditer(r'(?m)^(Theorem|Triviality)\s+([A-Za-z0-9_\']+)(\[[^\]]*\])?\s*=(.*?)(?=^\S)',s,re.S):
        hol.setdefault(m.group(2),(f,'(derived)',m.group(4).strip()))
    for m in re.finditer(r'(?m)^val\s+([A-Za-z0-9_\']+)\s*=\s*(?:Q\.)?(?:store_thm|prove)\s*\(.*?\);',s,re.S):
        hol.setdefault(m.group(1),(f,'(store_thm)',m.group(0)))
# Lean proofs
lean={}
for f in sorted(os.listdir('LeanTypeSound')):
    clean=strip_lean_comments(open('LeanTypeSound/'+f,newline='').read().replace('\r',''))
    ms=list(DECL_RE.finditer(clean))
    for i,m in enumerate(ms):
        end=ms[i+1].start() if i+1<len(ms) else len(clean)
        if m.group('kind') in ('theorem','lemma'):
            lean[(f,m.group('name'))]=clean[m.start():end]
allbyname={}
for (f,n),c in lean.items(): allbyname.setdefault(n,[]).append((f,c))
rows=[]
for t in canon:
    n=t['name']; c=lean[(t['file'],n)]
    st=re.sub(r'\s+','',t['statement'])
    cc=re.sub(r'\s+',' ',c)
    # proof text = after statement
    idx=len(t['statement'])
    proof=c[c.index(':=',max(0,len(c)-len(c)) if False else 0):] if False else None
    # locate ':=' following statement by whitespace-insensitive match
    j=0;k=0
    while k<len(st) and j<len(c):
        if c[j].isspace(): j+=1; continue
        assert c[j]==st[k],(n,c[j],st[k]); j+=1;k+=1
    proof=c[j:].strip()
    proof=re.sub(r'(set_option\s+\S+\s+\S+\s+in\s*)+$','',proof).strip()
    plines=len([l for l in proof.splitlines() if l.strip()])
    # follow single delegation `:= DAux.name'` etc
    m=re.fullmatch(r":=\s*(?:by\s+exact\s+)?([A-Za-z0-9_.']+)\s*",proof)
    deleg=None
    if m:
        d=m.group(1).split('.')[-1]
        if d in allbyname:
            deleg=d; plines=len([l for l in allbyname[d][0][1].splitlines() if l.strip()])
    hn=n if n in hol else re.sub(r'_(thm|local)$','',n)
    h=hol.get(hn)
    hl=len([l for l in h[2].splitlines() if l.strip()]) if h else -1
    rows.append((n,t['file'],hl,plines,deleg,proof[:100].replace('\n',' ')))
json.dump(rows,open('/home/claude/work/compare_rows.json','w'))
missing=[r[0] for r in rows if r[2]<0]
print('canonical',len(rows),'no HOL4 match:',missing)
print('HOL4 proof lines total',sum(r[2] for r in rows if r[2]>0),'Lean proof lines (direct or one delegation)',sum(r[3] for r in rows))
print('\nHOL4 >= 8 lines but Lean <= 3 lines:')
for r in rows:
    if r[2]>=8 and r[3]<=3: print('  ',r)
print('\nLean one-liners overall:',sum(1 for r in rows if r[3]<=1))
