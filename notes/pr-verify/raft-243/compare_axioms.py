# Compare `#print axioms` of two builds of a Results.lean, from their Lake traces:
#   python3 compare_axioms.py <lean>/.lake/build/lib/lean/Proof/go_etcd_io/raft/v3/Results.trace \
#     <branch>/.lake/build/lib/lean/Proof/go_etcd_io/raft/v3/Results.trace [NAME-REGEX]
# Prints the results whose axioms differ (CHANGED/NEW/GONE) and, for NAME-REGEX, the unchanged ones.
import json,re,sys
def load(p):
    d=json.load(open(p)); out={}
    for m in d['log']:
        t=m.get('message','')
        mm=re.search(r"'([^']+)' depends on axioms: \[(.*)\]",t,re.S)
        if mm: out[mm.group(1)]=set(x.strip() for x in mm.group(2).split(',') if x.strip())
        mm=re.search(r"'([^']+)' does not depend on any axioms",t)
        if mm: out[mm.group(1)]=set()
    return out
a=load(sys.argv[1]); b=load(sys.argv[2])
print('results: lean', len(a), 'branch', len(b))
pat=re.compile(sys.argv[3]) if len(sys.argv)>3 else None
sor_a=[k for k in a if 'sorryAx' in a[k]]; sor_b=[k for k in b if 'sorryAx' in b[k]]
print('reaching sorryAx: lean', len(sor_a), 'branch', len(sor_b))
for k in sorted(set(a)|set(b)):
    if k not in a: print('NEW', k, len(b[k]), 'sorry' if 'sorryAx' in b[k] else ''); continue
    if k not in b: print('GONE', k); continue
    if a[k]!=b[k]:
        print('CHANGED', k, '+', sorted(b[k]-a[k]), '-', sorted(a[k]-b[k]))
    elif pat and pat.search(k): print('SAME', k, len(a[k]))
