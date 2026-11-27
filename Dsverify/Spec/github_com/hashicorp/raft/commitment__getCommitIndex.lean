/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/commitment__getCommitIndex.lean (241f27e).
-/
/-
`raft.(*commitment).getCommitIndex`'s spec (raft-internal interface, notes/raft-iface.md). `0` or a recorded commit of `T`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*commitment).getCommitIndex`: `0`, or past `T`'s election part and covered by a recorded commit of
`T` (stage 3, C1: with `lciOk` matches the commit is recorded at some `k ≥ c`). -/
abbrev github_com.hashicorp.raft.commitment.getCommitIndex.spec : Prop :=
  ∀ (γ : GNames) (i : SID) (T : Nat) (cm : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isCommitment γ i T cm }}
    (App (Val (cm @!! go.GoType.PointerType commitment.ty @!! go!"getCommitIndex")) (Val #()))
  {{ (c : w64), RET #c; ⌜c = W64 0⌝ ∨
       ∃ n0 k p, len0Is γ T n0 ∗ ⌜n0 < uint.nat c ∧ uint.nat c ≤ k⌝ ∗ commitIs γ T k p }}

end spec

end Perennial
