import os,re,sys
root=sys.argv[1]; target=sys.argv[2]
mods={}
for d in ["Code","GeneratedProof","Spec","Proof"]+[x for x in os.listdir(root) if os.path.isdir(os.path.join(root,x)) and x[0].isupper() and x not in("Code","GeneratedProof","Spec","Proof")]:
  for dp,_,fs in os.walk(os.path.join(root,d)):
    for f in fs:
      if f.endswith(".lean"):
        p=os.path.join(dp,f); m=os.path.relpath(p,root)[:-5].replace("/",".")
        imps=re.findall(r'^(?:public |meta )*import\s+(\S+)',open(p).read(),re.M)
        mods[m]=imps
rev={}
for m,i in mods.items():
  for x in i: rev.setdefault(x,[]).append(m)
seen=set();st=[target]
while st:
  x=st.pop()
  for y in rev.get(x,[]):
    if y not in seen: seen.add(y);st.append(y)
for m in sorted(seen):
  if m.endswith(".Link") or m.endswith(".Results"): print(m)
print(len(seen),file=sys.stderr)
