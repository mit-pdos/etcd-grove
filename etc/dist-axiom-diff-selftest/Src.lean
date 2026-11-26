/- `etc/dist-axiom-diff.py --selftest`'s in-process source (not built: read as text only). -/
abbrev st.spec : Prop :=
  ∀ (cfg : Cfg) (γn : NetNames GF),
  -- a pure premise the copy must keep
  etcdURLsFit cfg.peer →
  {{ "Htok" ∷ threadTok ∗ "#Hnet" ∷ netHttpOk γn ∗ "%Hγn" ∷ ⌜γn.N = srvNet⌝ }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc), RET #srv; threadTok ∗ srvBuilt srv }}
