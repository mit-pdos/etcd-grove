/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/max.lean (241f27e).
-/
/-
`raft.max`'s spec: the unsigned maximum of two `uint64`s (no panic).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `raft.max(a, b)` returns the unsigned maximum of `a` and `b`. -/
abbrev github_com.hashicorp.raft.max.spec : Prop :=
  ∀ (a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (App (Val (@! github_com.hashicorp.raft.max)) (Val #a)) (Val #b))
  {{ RET #(if uint.Z a ≥ uint.Z b then a else b); True }}

end spec

end Perennial

