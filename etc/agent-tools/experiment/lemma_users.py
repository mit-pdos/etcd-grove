import re, glob, os, collections
R = '/home/ubuntu/.claude/jobs/f5d25fd8/tmp/btree-src/EtcdGrove/Btree'
CH = ['node__get', 'node__insert']
lemma_files = glob.glob(R + '/Lemmas/*.lean') + [R + '/ListLemmas.lean', R + '/NodeLemmas.lean']
decl = re.compile(r'^(?:private |protected )?(?:theorem|lemma|def|abbrev)\s+([\w.''?]+)', re.M)
proofs = {os.path.basename(p)[:-5]: open(p).read() for p in glob.glob(R + '/Proof/*.lean')}
others = {os.path.basename(p): open(p).read() for p in lemma_files}
for ch in CH:
    imps = re.findall(r'^import (\S+)', proofs[ch], re.M)
    print(ch, 'imports', [i.split('.')[-1] for i in imps])
for lf in lemma_files:
    src = open(lf).read()
    names = decl.findall(src)
    only = collections.defaultdict(list)
    for n in names:
        short = n.split('.')[-1]
        pat = re.compile(r'(?<![\w.])' + re.escape(short) + r'(?![\w''])')
        users = [p for p, s in proofs.items() if pat.search(s)]
        lusers = [f for f, s in others.items() if f != os.path.basename(lf) and pat.search(s)]
        # used inside its own file by other lemmas?
        own_uses = len(pat.findall(src)) - 1
        key = tuple(sorted(u for u in users if u in CH))
        if users and set(users) <= set(CH) and not lusers:
            only[key].append(n)
    for k, v in only.items():
        print(os.path.basename(lf), k, len(v), v)
