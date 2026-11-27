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

/- The auth-on copy of `SrcOn.lean`'s theorem `st_on` (the registration replaced by the view's client). -/
abbrev st_on_dist.spec [π : NetProtoGS] : Prop :=
  ∀ (api : Loc) (k : GoString) (Γ : DistView), k ≠ [] →
    {{ threadTok ∗ userClientAt api Γ ∗ writeAuD Γ.kv (.put k) Q }}
      (App (Val (api @!! go!"Put")) (Val #k))
    {{ (m : PutRespM), RET #m; threadTok ∗ putReplied E k Q m ∗ writeCheckedD Γ k }}

/- The same copy claiming a conjunct the theorem does not give (`kvRevLb`, as the auth-off spec's):
the selftest pairs it under `st_on_dist`'s lines, and the gate must refuse it. -/
abbrev st_onbad_dist.spec [π : NetProtoGS] : Prop :=
  ∀ (api : Loc) (k : GoString) (Γ : DistView), k ≠ [] →
    {{ threadTok ∗ userClientAt api Γ ∗ writeAuD Γ.kv (.put k) Q }}
      (App (Val (api @!! go!"Put")) (Val #k))
    {{ (m : PutRespM), RET #m; threadTok ∗ putReplied E k Q m ∗ kvRevLb Γ.kv m.rev ∗ writeCheckedD Γ k }}

axiom st_on_dist : st_on_dist.spec
