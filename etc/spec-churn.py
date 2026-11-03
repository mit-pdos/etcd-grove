#!/usr/bin/env python3
"""Spec churn from the git log: how often a statement changes after a spec-first stage froze it,
against after a proof-first touch (notes/spec-first-plan.md, "Spec churn from the git log").

Usage, from the repository root: python3 -I etc/spec-churn.py [--ref REF]   (about a minute)

Unit: a declaration of the statement surface (Spec/ and the shared Proof/ modules: Inv*, Api*,
Defs, Base*, ...; RaftWitness's too).

A declaration's statement: a theorem's/axiom's/instance's type (up to its `:=`), a definition's whole
text (its body is part of what statements mean). Comments, attributes, whitespace stripped; private
declarations and the function proof files (Proof/<pkg>/<fn>.lean with a Spec/ twin), Link, Results
and Init are left out. Key: (directory, name), so a move between files of one directory is no change.

Cohorts:
- spec-first: the declarations a stage's commits (subject matching the stage's prefix) created or
  changed in the six days up to its freeze commit (STAGES below; add a stage when it freezes). The
  clock starts at the freeze. Stages that froze a design in notes before writing Lean (raft unified,
  the decision switch, txn-nested) touch no declaration and show as "none".
- proof-first: a declaration written by a commit of no stage and then unchanged for 12h ("settled");
  its first such point in the period. There is no proof-first point matching a freeze, so this
  baseline is the weak part: it is diluted by leaf declarations nobody returns to.
"Targeted": a change in a commit changing at most CROSS declarations (not a project-wide rewrite).
"Own-stage": a change by a commit of the stage that froze the declaration (the review's misses);
the last table lists which commits changed each stage's declarations.
"""
import re, subprocess, collections, datetime, os, sys, argparse
ap=argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
ap.add_argument("--ref",default="lean")
REF=ap.parse_args().ref
def git(*a): return subprocess.run(["git",*a],capture_output=True,text=True,check=True).stdout
log=git("log",REF,"--no-merges","--reverse","-M","--name-status","--format=@@%H|%at|%s","--",
        "Spec","Proof","RaftWitness/Spec","RaftWitness/Proof")
commits=[];cur=None
for line in log.splitlines():
    if line.startswith("@@"):
        h,t,s=line[2:].split("|",2);cur={"h":h,"t":int(t),"s":s,"files":[]};commits.append(cur)
    elif line.strip() and cur:
        p=line.split("\t");st=p[0]
        cur["files"].append(("R",p[1],p[2]) if st.startswith("R") else (st[0],p[1],None))
# spec files ever: their proof twins are function proofs
specs_ever=set()
for c in commits:
    for st,p,q in c["files"]:
        for x in (p,q):
            if x and x.endswith(".lean") and (x.startswith("Spec/") or x.startswith("RaftWitness/Spec/")): specs_ever.add(x)
def surface_file(p):
    if not p.endswith(".lean"): return False
    if not (p.startswith(("Spec/","Proof/","RaftWitness/Spec/","RaftWitness/Proof/"))): return False
    b=os.path.basename(p)
    if b in ("Link.lean","Results.lean","Init.lean","Initialize.lean"): return False
    if "/Proof/" in "/"+p and p.replace("Proof/","Spec/",1) in specs_ever: return False
    return True
cat=subprocess.Popen(["git","cat-file","--batch"],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(h,p):
    cat.stdin.write(f"{h}:{p}\n".encode());cat.stdin.flush()
    hdr=cat.stdout.readline().decode()
    if hdr.endswith("missing\n"): return None
    n=int(hdr.split()[2]);d=cat.stdout.read(n);cat.stdout.read(1);return d.decode("utf-8","replace")
def uncomment(src):
    out,i,depth,n=[],0,0,len(src)
    while i<n:
        if src.startswith("/-",i): depth+=1;i+=2;continue
        if depth and src.startswith("-/",i): depth-=1;i+=2;continue
        if depth:
            if src[i]=="\n": out.append("\n")
            i+=1;continue
        if src.startswith("--",i):
            j=src.find("\n",i);i=n if j<0 else j;continue
        out.append(src[i]);i+=1
    return "".join(out)
DECL=re.compile(r"^((?:private |protected |noncomputable |partial |nonrec |unsafe )*)(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)\b(.*)")
CONT=re.compile(r"^(\s|\||where\b|deriving\b|$)")
def decls(src):
    s=re.sub(r"@\[[^\]]*\]","",uncomment(src))
    res={};curk=None;buf=[]
    def flush():
        if curk is None: return
        mods,kw,name=curk
        toks=re.findall(r"\S+"," ".join(buf))
        if kw in ("theorem","lemma","instance","axiom"):
            cut=next((i for i,t in enumerate(toks) if t.startswith(":=")),len(toks))
            toks=toks[:cut]
        if "private" not in mods: res[name]=(kw,toks)
    for line in s.split("\n"):
        m=DECL.match(line)
        if m:
            flush();rest=m.group(3).split()
            name=rest[0] if rest and kw_named(m.group(2),rest[0]) else "instance:"+" ".join(rest[:8])
            curk=(m.group(1),m.group(2),name);buf=[line]
        elif curk and CONT.match(line): buf.append(line)
        else: flush();curk=None;buf=[]
    flush();return res
def kw_named(kw,tok): return not (kw=="instance" and (tok.startswith(":") or tok.startswith("[") or tok.startswith("(") or tok.startswith("{")))

files=collections.defaultdict(dict)   # dir -> {path: {name:(kw,toks)}}
dirmap=collections.defaultdict(dict)  # dir -> {name:(kw,toks)}
created={}; changes=collections.defaultdict(list); kinds={}; nchg={}; touched=collections.defaultdict(set)
for c in commits:
    aff=set()
    for st,p,q in c["files"]:
        if st=="R":
            files[os.path.dirname(p)].pop(p,None); aff.add(os.path.dirname(p)); path=q
        else: path=p
        if not surface_file(path): continue
        d=os.path.dirname(path); aff.add(d)
        if st=="D": files[d].pop(path,None); continue
        src=blob(c["h"],path)
        if src is None: continue
        files[d][path]=decls(src)
    ch=[]
    for d in aff:
        new={}
        for p in sorted(files[d]): new.update(files[d][p])
        old=dirmap[d]
        for name,(kw,toks) in new.items():
            k=(d,name)
            if name not in old:
                created.setdefault(k,c["t"]); kinds[k]=kw; touched[c["h"]].add(k)
            elif old[name][1]!=toks: ch.append(k); touched[c["h"]].add(k)
        dirmap[d]=new
    nchg[c["h"]]=len(ch)
    for k in ch: changes[k].append((c["t"],c["h"],c["s"]))
# (name, subject regex of its commits, freeze commit); backend-cmp and lease-revoke have no freeze
# commit: the end of their Probe step stands in.
STAGES=[("compactor",r"^compactor","c287014421"),("M2",r"^M2\b","51387263cb"),
 ("raft unified",r"^raft (unified|U8)","c962f759a2"),("decision switch",r"^raft (unified|U8)","0b29671ea6"),
 ("backend-cmp",r"^backend-cmp","23e933c777"),
 ("G2",r"^G2\b","f340de6db2"),("authkv",r"^authkv","c15854543d"),("txn-nested",r"^txn-nested","3c15ab5252"),
 ("lease-keys",r"^lease-keys","21cd348f6b"),("lease-revoke",r"^lease-revoke","46726f0b33"),
 ("lease keep-alive",r"^lease keep-alive","c903a965f4"),("lease-src",r"^lease-src","4da9663c72")]
NOW=int(datetime.datetime.now(datetime.timezone.utc).timestamp())
ERA=int(datetime.datetime(2026,10,27,tzinfo=datetime.timezone.utc).timestamp())
H=3600; CROSS=40
ETCD=re.compile(r"^(Spec|Proof)/(go_etcd_io/etcd/|github_com/mit_pdos/etcd_grove/examples/)")
stagecommit=set(); sf=[]
for name,rx,fz in STAGES:
    tf=int(git("log","-1","--format=%at",fz))
    ks=set()
    for c in commits:
        if re.search(rx,c["s"],re.I) and tf-6*86400<c["t"]<=tf: ks|=touched[c["h"]]; stagecommit.add(c["h"])
    for k in ks: sf.append((name,rx,k,tf))
for c in commits:
    if any(re.search(rx,c["s"],re.I) for _,rx,_ in STAGES): stagecommit.add(c["h"])
sfkeys={k for _,_,k,_ in sf}
def win(k,t0,D,gap=0): return [x for x in changes[k] if t0+gap<x[0]<=t0+D*86400]
def lemma(k): return kinds.get(k) in ("theorem","lemma")
def report(label,L,D,gap=0):
    L=[x for x in L if x[1]+D*86400<=NOW]
    if not L: print(f"  {label:44} (none old enough)"); return
    n=len(L); c=t=0
    for k,t0 in L:
        w=win(k,t0,D,gap)
        if w: c+=1
        if [x for x in w if nchg[x[1]]<=CROSS]: t+=1
    print(f"  {label:44} {n:6} {100*c/n:6.1f}% changed  {100*t/n:6.1f}% targeted")
# baseline: proof-first touches -- a non-stage commit creates/changes a declaration's statement, and the
# declaration is then unchanged for 12h ("settled"); first such point per declaration in the period.
def baseline(lo,hi,filt):
    out={}
    for c in commits:
        if not (lo<=c["t"]<hi) or c["h"] in stagecommit: continue
        for k in touched[c["h"]]:
            if k in out or k in sfkeys or not filt(k): continue
            if any(c["t"]<x[0]<=c["t"]+12*H for x in changes[k]): continue
            out[k]=c["t"]
    return list(out.items())
etcd=lambda k: bool(ETCD.search(k[0]+"/"))
for D in (2,4):
    print(f"\n== within {D} days (stage: of its freeze; proof-first: of a settled touch); declarations")
    for kindname,kf in (("definitions/abbrevs/structures",lambda k: not lemma(k)),("theorem statements",lemma)):
        print(f" {kindname}:")
        L=[(k,t0) for _,_,k,t0 in sf if kf(k)]
        report("spec-first, all stages",L,D)
        report("spec-first, all stages, changes after 12h",L,D,12*H)
        report("proof-first etcd 10-17..10-27",[x for x in baseline(ERA-10*86400,ERA,etcd) if kf(x[0])],D)
        report("proof-first etcd since 10-27",[x for x in baseline(ERA,NOW,etcd) if kf(x[0])],D)
        report("proof-first all 10-17..10-27",[x for x in baseline(ERA-10*86400,ERA,lambda k:True) if kf(x[0])],D)
print("\n== per stage: changed within 2 days of the freeze (definitions | theorems), own-stage changes")
for name,rx,fz in STAGES:
    L=[(k,t0) for n2,_,k,t0 in sf if n2==name]
    if not L: print(f"  {name:18} none"); continue
    t0=L[0][1]
    defs=[k for k,_ in L if not lemma(k)]; ths=[k for k,_ in L if lemma(k)]
    cd=[k for k in defs if win(k,t0,2)]; ct=[k for k in ths if win(k,t0,2)]
    own=[k for k,_ in L if any(re.search(rx,x[2],re.I) for x in win(k,t0,2))]
    young=" (window not complete)" if t0+2*86400>NOW else ""
    print(f"  {name:18} defs {len(cd):3}/{len(defs):4}  theorems {len(ct):3}/{len(ths):4}  own-stage {len(own):3}{young}  e.g. {', '.join(k[1] for k in cd[:4])}")
print("\n== who changed stage declarations within 2 days of the freeze (commits, declarations changed)")
for name,rx,fz in STAGES:
    L=[(k,t0) for n2,_,k,t0 in sf if n2==name]
    if not L: continue
    cnt=collections.Counter()
    for k,t0 in L:
        for x in win(k,t0,2): cnt[(x[2][:90],nchg[x[1]])]+=1
    print(f" {name}:")
    for (s,n),v in cnt.most_common(5): print(f"   {v:3}  [{n:4} in commit] {s}")
