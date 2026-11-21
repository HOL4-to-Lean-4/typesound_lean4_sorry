import json,sys,re,collections
tools=collections.Counter(); bad=[]
pat=re.compile(r'typesound_lean4_sorry|hol4-ultramin|/mnt/|candle-hol4|typesound_lean4\b|github\.com|https?://|git (log|show|clone|fetch|checkout)|/home/claude/work/ws[A-D]|/home/claude/work/base|/home/claude/work/merged')
me=sys.argv[2]
for line in open(sys.argv[1]):
    try: d=json.loads(line)
    except Exception: continue
    msg=d.get('message',{})
    c=msg.get('content') if isinstance(msg,dict) else None
    if not isinstance(c,list): continue
    for b in c:
        if isinstance(b,dict) and b.get('type')=='tool_use':
            tools[b['name']]+=1
            s=json.dumps(b.get('input',{}))
            for m in pat.finditer(s):
                if m.group(0).endswith(me): continue
                bad.append((b['name'],m.group(0),s[max(0,m.start()-80):m.start()+120]))
print(dict(tools)); print('suspicious references:',len(bad))
for x in bad[:10]: print(x)
