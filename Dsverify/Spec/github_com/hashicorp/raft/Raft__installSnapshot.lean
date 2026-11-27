/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__installSnapshot.lean (241f27e).
-/
/-
`raft.(*Raft).installSnapshot`'s spec (stage 3, raft-internal: the main goroutine's handler of an InstallSnapshot RPC; crosses the snapshot store, the FSM goroutine and the log store).
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

/-- `(*Raft).installSnapshot(rpc, req)`, by the main goroutine (`processRPC`), for an InstallSnapshot
`RPC` delivered to `i` (`iface.isRpcP`: the request `req`, valid, its snapshot stream as `rpc.Reader`,
its response channel): responds once (success or not, or an unformatted error). A request of an older
term is refused; a newer term makes `i` a follower in it; a snapshot at or below the FSM position is
acknowledged without installing (the rollback guard, fix `db9dde4`); otherwise the snapshot is copied
into a new sink and closed (it becomes the store's latest: the pending install, `snapCell`), restored
by the FSM goroutine (a restore future on `fsmMutateCh`, `fsmRestoreP`), `lastApplied` becomes its
index, the last snapshot and both configurations are set (the latest in its invariant cell, review
T1-6), and the log is kept (the install is a `learnCommit` of the index: `learnCommitFollower` with no
entries) and compacted if it holds the snapshot's last entry, or replaced by the committed prefix
(`installDiscard_upd`, fix `5c0b97e`); either way the durable prefix reaches the index. Unless `i` becomes a follower its term is unchanged, and its
log too, or it is a candidate of a term whose leader is another server (as `processRPC`). -/
abbrev github_com.hashicorp.raft.Raft.installSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (req : Loc) (s : SState) (st : w32)
    (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
      mainOwnAt r γ rc i s st ∗ isRpcP γ rc.snapP i rpc ∗
      ⌜rpc.Command' = interface.mkOk (go.GoType.PointerType InstallSnapshotRequest.ty) #req⌝ ∗
      rtok tid }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"installSnapshot")) (Val #rpc))
      (Val #req))
  {{ RET #(); ∃ (s' : SState) (st' : w32), mainOwnAt r γ rc i s' st' ∗ rtok tid ∗
      (⌜st' = stFollower ∨ (st' = st ∧ s'.term = s.term ∧ s'.log = s.log)⌝ ∨
       ⌜st' = st ∧ st = stCandidate ∧ s'.term = s.term⌝ ∗ ∃ ℓ : SID, ⌜ℓ ≠ i⌝ ∗ leaderIs γ s.term ℓ) }}

end spec

end Perennial
