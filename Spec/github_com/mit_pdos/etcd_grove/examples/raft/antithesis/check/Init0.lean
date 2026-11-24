/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `Init0(cfg)`: `init0`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- B 755-764 `Init0`: `init0`'s state, where defined, read-only. -/
abbrev Init0.spec : Prop :=
  ∀ (cp : Loc) (cfg : Config) (s : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      configRO cp cfg ∗ ⌜init0 cfg = .ok s ∧ Config.Bounded cfg⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0)) (Val #cp))
  {{ (p : Loc), RET #p; stateRO p s }}

end spec

end AntCheck
end EtcdGrove
end Perennial
