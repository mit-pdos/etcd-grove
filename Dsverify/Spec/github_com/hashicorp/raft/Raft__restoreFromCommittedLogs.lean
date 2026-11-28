/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__restoreFromCommittedLogs.lean (241f27e).
-/
/-
`raft.(*Raft).restoreFromCommittedLogs`'s spec (API-internal, `NewRaft`'s): with `RestoreCommittedLogs` on, the
commit index the log store wrote becomes the server's, and the entries up to it are applied.
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

/-- `(*Raft).restoreFromCommittedLogs`, called by `NewRaft` (hraft_robust rcl; was: `RestoreCommittedLogs`
false, nothing): with `RestoreCommittedLogs` off, nothing; on (the log store then a `CommitTrackingLogStore`,
else `ErrIncompatibleLogStore`), the commit index `k` the store wrote (`GetCommitIndex`, at most `LastIndex`),
which is durable (`k ≤ s.dur.1`), becomes the main goroutine's commit index (`setCommitIndex`) and the
entries up to it are applied (`processLogs`, from the applied index `a`). Over `isRaftCore`: `NewRaft` still
pins `lastLock`'s fields. -/
abbrev github_com.hashicorp.raft.Raft.restoreFromCommittedLogs.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (b : Bool) (x : GoInterfaceOk) (s : SState)
    (a c tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaftCore r γ rc i ∗
     r.[Raft, go!"RestoreCommittedLogs"] ↦□ b ∗ r.[Raft, go!"logs"] ↦□ (GoInterface.ok x) ∗
     ⌜b = false ∨ go.typeSetContains x.ty CommitTrackingLogStore.ty = true⌝ ∗
     srvV rc s ∗ fsmProd γ rc a ∗ monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
     monoNatAuthOwn rc.dur.comp (1 : Qp).half c ∗ ⌜c ≤ a ∧ s.cidx ≤ a⌝ ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"restoreFromCommittedLogs")) (Val #()))
  {{ RET #interface.nil; ∃ k : Nat, ⌜(b = false ∧ k = s.cidx) ∨ (b = true ∧ k ≤ s.dur.1)⌝ ∗
      srvV rc { s with cidx := k } ∗ fsmProd γ rc (Max.max a k) ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half (Max.max a k) ∗
      monoNatAuthOwn rc.dur.comp (1 : Qp).half c ∗ rtok tid }}

end spec

end Perennial
