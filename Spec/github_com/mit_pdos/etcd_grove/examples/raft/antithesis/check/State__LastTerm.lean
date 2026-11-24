/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.LastTerm(i)`.
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

/-- R 132 `LastTerm(i)`: `State.lastTerm`. -/
abbrev State.LastTerm.spec : Prop :=
  ∀ (p : Loc) (s : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < s.cfg.server.length⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"LastTerm")) (Val #i))
  {{ (w : w64), RET #w; ⌜sint.Z w = s.lastTerm (sint.nat i)⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
