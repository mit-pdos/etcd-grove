/- `etc/dist-axiom-diff.py --selftest`'s copy (not built: read as text only): `st.spec` with the
network fact replaced, the network names moved to the post, and the premise `etcdURLsFit` dropped
(the drift the gate exists for; listed in `allow.txt`, so that removing the line must fail). -/
abbrev st_dist.spec [π : NetProtoGS] : Prop :=
  ∀ (cfg : Cfg),
  {{ "Htok" ∷ threadTok ∗ "#Hpeers" ∷ peersAt cfg }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc), RET #srv; threadTok ∗ ∃ γn, ⌜γn.N = srvNet⌝ ∗ srvBuilt srv }}

axiom st_dist : st_dist.spec
axiom st_nosrc_dist : True
