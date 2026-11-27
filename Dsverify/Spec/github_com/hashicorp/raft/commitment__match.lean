/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/commitment__match.lean (241f27e).
-/
/-
`raft.(*commitment).match`'s spec (raft-internal interface, notes/raft-iface.md). Records that voter `j` acknowledged `k` entries in term `T` (or `k = 0`); may raise the commit index (`commit_upd`).
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

/-- `(*commitment).match`: Records that voter `j` acknowledged `k` entries in term `T` (or `k = 0`; stage 3, check N4: or a valid install's commit index of `T`, `lciOk`, counted by
`sendLatestSnapshot`); may raise the commit index (`commit_or_snap`). -/
abbrev github_com.hashicorp.raft.commitment.match.spec : Prop :=
  ∀ (γ : GNames) (i : SID) (T : Nat) (cm : Loc) (j : ServerID) (k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isCommitment γ i T cm ∗ (⌜uint.nat k = 0⌝ ∨ ackIs γ j T (uint.nat k) ∨ lciOk γ T (uint.nat k)) }}
    (App (App (Val (cm @!! go.GoType.PointerType commitment.ty @!! go!"match")) (Val #j)) (Val #k))
  {{ RET #(); True }}

end spec

end Perennial
