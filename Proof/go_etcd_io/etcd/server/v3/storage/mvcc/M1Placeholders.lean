/-
**Placeholders of the M1 migration** (strict M1, 2026-11-04: `notes/decisions.md`, "strict M1, no
scaffold"). Lean-first (no Rocq counterpart).

The store's locks hold the API's ghost state outright (`InvStore`'s slots at `StoreNames.api`).
Today's specs of the methods that move it (`storeTxnWrite.End`, `store.updateCompactRev`,
`store.Write`'s checkout; the watchable store's `End`, `Restore` and constructor) give their callers none of the client's parts, so their proofs cannot
take the API's steps; each such step is one of the lemmas below, **false in general** and proved
by `sorry`, marked `M1-REPLACE` with the API contract whose proof replaces it at stage 2 (the
proofs using them are rewritten against the API's contracts, and this module goes). Nothing new
may use them. (Elsewhere, listed: `RestoreMoves`' five local ones; `Api/NewStoreApi.lean`'s `mvccDeleter_M1`, the
range deleter's contract, M1-REPLACE: `KV.Write.contract`.)
(M4 track B, 2026-11-06) `slotX_step_M1` and `slotY_step_M1` are gone, and `slotF_excl_M1`'s and
`wsSlot_step_M1`'s uses by the `End`s: the internal `End`s take the moves of the API's slots as their
caller's ghost steps (`Api/TxnSteps.lean`: `endCb`, `wsEndCb`) and the frozen state's excluder `G`.

The snapshot image's store-side tracking (2026-11-05, `notes/mvcc-api-invariants.md`, "the snapshot
image's tracking in place"): the batch lock's resource pins the tracked compaction (`cmpTrack`), so
the steps that move it must re-establish it; all are proved (`cmpTrack_new_M1` is gone, track A,
2026-11-06: `NewStore`'s `cmpTrack_fresh`, `store.Restore`'s `cmpTrack_restored` from the image; the
job's, `cmpTrack_job_M1`, is gone: the job's cursor and its per-entry cut, `Api/CmpJob.lean`,
2026-11-06; `regLent_excl_M1` and `rcvSched_M1` are gone: `updateCompactRev` fires its caller's ghost
step, `cmpCb`, inside `SetScheduledCompact`'s loan, with the writer's state found checked in, the
frozen and restoring states excluded by the caller's share, `KV.Compact.contract`, 2026-11-06).
`snapObs_M1` (the frozen store's part of a snapshot's observation) is gone:
`mvccImage_snapshot.law_holds` is proved. `wsSlot_make_M1` (the watchable store's lock's slot) is
gone: `newWatchableStore` makes it from the client's parts `NewStore` returns (track A, 2026-11-06). `hookNilRO_M1` (2026-11-06) is gone: §4.8, a store without
a hook (`batchTxSpecG`'s nil-hook clause at any share of the hook at `nil`, `kbHookNilAt`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI

section placeholders
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **(Placeholder, false in general.)** The frozen state excluded without a share of the token.
M1-REPLACE: `KV.Write.contract` (the writer's backend share, `mvccBackend γ q`, excludes it:
`slotF_share_excl`; `End`'s uses are gone: its caller's excluder `G`, M4 track B, 2026-11-06,
`Api/TxnSteps.lean`); `KV.Restore.contract` (`restore()`'s resumed
compaction, `compactLockfree`'s excluder: the restorer's share). -/
theorem slotF_excl_M1 (γ : StoreNames) : slotF (GF := GF) γ ∗ iprop(emp) ⊢ False := by
  sorry -- M1-REPLACE: KV.Write.contract, KV.Restore.contract (the backend share)

/-- **(Placeholder, false in general.)** A share of the writer's and `s.mu`'s compaction revision
(`api.AbsNames.wcr`, M4 track B, 2026-11-06) made from nothing, at the restored compaction revision.
M1-REPLACE: `KV.Restore.contract` (`store.Restore` moves the old halves, `s.mu`'s from its `muInvAt`
and the writer's from the old writer's `slotY`, to `r.crev` with `api.wcrPart_update`; the hand-off,
"the writer's compaction revision tied to `s.mu`'s"). -/
theorem wcrRestore_M1 (a : api.AbsNames) (q : Qp) (c : Int) : ⊢ api.wcrPart (GF := GF) a q c := by
  sorry -- M1-REPLACE: KV.Restore.contract (the compaction revision's ghost moved by Restore)

end placeholders

section placeholdersW
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **(Placeholder, false in general.)** The watchable store's lock's slot moved to a new notified
log without the client's update. M1-REPLACE: `KV.Restore.contract` (the watchable `End`'s use is gone:
its caller's notify step `wsEndCb`, M4 track B, 2026-11-06). -/
theorem wsSlot_step_M1 {γ : WsNames} {q : Qp} {L : Log} (L' : Log) :
    wsSlot (GF := GF) γ q L ⊢ wsSlot γ q L' := by
  sorry -- M1-REPLACE: KV.Restore.contract

end placeholdersW

end mvcc
end EtcdGrove
end Perennial
