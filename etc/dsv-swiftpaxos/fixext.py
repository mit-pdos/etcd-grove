#!/usr/bin/env python3
"""Move ported files onto the fixed extension list (netShaExts) with SwiftNetPkgState/SwiftHyps GF."""
import re,sys
ATTR='attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp\n  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256\n'
H='Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps'
for f in sys.argv[1:]:
    s=open(f).read()
    t=re.sub(r'^variable \[GooseExts\] \[GooseSemantics\] \[GooseInterp\]( \[HasExt (Net\.)?netExt\])?(.*)$',
             lambda m: ('variable'+m.group(3)) if m.group(3).strip() else '', s, flags=re.M)
    t=re.sub(r'^variable\s*$\n','',t,flags=re.M)
    if 'netShaExts netShaExtsSemantics' not in t:
        t=re.sub(r'^(open [^\n]*)\n', lambda m: m.group(1)+(' Dsv' if 'Dsv' not in m.group(1).split() else '')+'\n\n'+ATTR, t, count=1, flags=re.M)
    t=re.sub(r'^(variable \[sem : go\.Semantics\])(.*)$',
             lambda m: m.group(0) if 'SwiftHyps' in m.group(2) else m.group(1)+m.group(2)+'\nvariable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF]', t, flags=re.M)
    if H not in t:
        t=re.sub(r'^(public import [^\n]+\n)',r'\1public import '+H+'\n',t,count=1,flags=re.M)
    if t!=s: open(f,'w').write(t); print('fixed',f)
