/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__setCommitIndex.lean (241f27e).
-/
/-
`raft.(*raftState).setCommitIndex`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted). The protocol step at the store (`setCidx_upd`) is the caller's ghost update.
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

/-- `(*raftState).setCommitIndex`: Called through `*Raft` (promoted). The protocol step at the store (`setCidx_upd`) is the caller's ghost update. -/
abbrev github_com.hashicorp.raft.raftState.setCommitIndex.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (i : SID) (c : w64) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ cidxCell r γ i ∗
     (∀ c0 : Nat, cidxCouple γ i c0 ={⊤ \ ↑cidxN}=∗ cidxCouple γ i (uint.nat c) ∗ Q) }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setCommitIndex")) (Val #c))
  {{ RET #(); Q }}

end spec

end Perennial
