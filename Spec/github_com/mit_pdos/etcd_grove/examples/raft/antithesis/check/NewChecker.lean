/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `NewChecker(cfg)`: `check.go`, the checker at `init0`.
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

/-- The checker at `Init0` (`{ state := s }`, no verdict). -/
abbrev NewChecker.spec : Prop :=
  ∀ (cp : Loc) (cfg : Config) (s : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      configRO cp cfg ∗
      ⌜Config.Bounded cfg ∧ init0 cfg = .ok s⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.NewChecker)) (Val #cp))
  {{ (p : Loc), RET #p; checkerOwn p { state := s } }}

end spec

end AntCheck
end EtcdGrove
end Perennial
