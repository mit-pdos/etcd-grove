import re,sys
p=sys.argv[1]
s=open(p).read()
# delete the two theorems
s=re.sub(r"/-- `r\.stepDownOnRemoval` \(2026-10-13, reconfiguration stage A2\): `NState\.sdr`\. -/\ntheorem raft\.wp_load_stepDownOnRemovalC.*?resealC c s\n\n/-- The field `stepDownOnRemoval`, persistent.*?resealC c s\n\n","",s,flags=re.S)
s=re.sub(r"theorem raftOwn_sdr .*?iexact H_stepDownOnRemoval\n\n","",s,flags=re.S)
s=s.replace("""    -- (2026-10-14, stage B7 part 2) never written after `newRaft`: persistent, so that a
    -- client of a step learns it unchanged (`ownRaftPhysC_sdr`)
    "#H_stepDownOnRemoval" ∷ l.[raft, go!"stepDownOnRemoval"] ↦□ v.stepDownOnRemoval' ∗
""","")
s=s.replace("  ipersist stepDownOnRemoval\n","")
s=s.replace("H_stepDownOnRemoval ","")
s=s.replace("""  -- `r.stepDownOnRemoval` (2026-10-13, reconfiguration stage A2), recorded
  "%Hsdr" ∷ ⌜rv.stepDownOnRemoval' = s.sdr⌝ ∗
""","")
s=s.replace("    rv.stepDownOnRemoval' = s.sdr →\n","")
s=s.replace(" Hsdr Hid_nz"," Hid_nz").replace(" Hsdr, Hid_nz"," Hid_nz")
open(p,'w').write(s)
