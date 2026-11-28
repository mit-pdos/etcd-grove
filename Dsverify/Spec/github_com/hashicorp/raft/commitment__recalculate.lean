/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/commitment__recalculate.lean (241f27e).
-/
/-
`raft.(*commitment).recalculate`'s spec (replication subsystem, internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

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

/-- `(*commitment).recalculate`, with the lock held: raises the commit index to the quorum's
match index when that is past the leader's election-time log (`commit_upd`). -/
abbrev github_com.hashicorp.raft.commitment.recalculate.spec : Prop :=
  ∀ (γ : GNames) (i : SID) (T : Nat) (cm : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ commitInv γ i T cm }}
    (App (Val (cm @!! go.GoType.PointerType commitment.ty @!! go!"recalculate")) (Val #()))
  {{ RET #(); commitInv γ i T cm }}

end spec

end Perennial
