/-
(hraft_robust R3) The spec of `disk.bytesEq` (`disk.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Codec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.disk in
/-- `bytesEq(a, b)`: whether the bytes are equal. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq.spec : Prop :=
  ∀ (a b : GoSlice) (dqa dqb : DFrac) (xs bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
      a ↦*{dqa} xs ∗ b ↦*{dqb} bs }}
    (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq)) (Val #a)) (Val #b))
  {{ RET #(decide (xs = bs)); a ↦*{dqa} xs ∗ b ↦*{dqb} bs }}

end spec

end Perennial
