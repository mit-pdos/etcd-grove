import re,sys
for p in sys.argv[1:]:
    s=open(p).read(); o=s
    s=re.sub(r"\n[ \t]*\"#Hsdrf\" ∷ sdrOk rnv\.raft' rs\.mode ∗","",s)
    s=re.sub(r"\n([ \t]*)sdrOk rnv\.raft' rs\.mode -∗","",s)
    s=s.replace(" -∗ sdrOk rnv.raft' rs.mode -∗"," -∗")
    s=s.replace(" #Hsdrf "," ").replace(" $Hsdrf "," ").replace(" Hsdrf "," ")
    if s!=o: open(p,'w').write(s); print(p)
