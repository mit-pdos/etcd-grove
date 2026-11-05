/-
**Placeholders of the M1 migration** (strict M1, 2026-11-04: `notes/decisions.md`, "strict M1, no
scaffold"). Lean-first (no Rocq counterpart).

The store's locks hold the API's ghost state outright (`InvStore`'s slots at `StoreNames.api`).
Today's specs of the methods that move it (`storeTxnWrite.End`, `store.updateCompactRev`,
`store.Write`'s checkout; the watchable store's `End`, `Restore` and constructor) give their callers none of the client's parts, so their proofs cannot
take the API's steps; each such step is one of the lemmas below, **false in general** and proved
by `sorry`, marked `M1-REPLACE` with the API contract whose proof replaces it at stage 2 (the
proofs using them are rewritten against the API's contracts, and this module goes). Nothing new
may use them. (Elsewhere, listed: `RestoreMoves`' five local ones.)

The snapshot image's store-side tracking (2026-11-05, `notes/mvcc-api-invariants.md`, "the snapshot
image's tracking in place"): the batch lock's resource pins the tracked compaction (`cmpTrack`), so
the steps that move it must re-establish it; those not yet proved are the three below
(`regLent_excl_M1`, `rcvSched_M1`, `cmpTrack_new_M1`; the job's, `cmpTrack_job_M1`, is gone: the job's
cursor and its per-entry cut, `Api/CmpJob.lean`, 2026-11-06). `snapObs_M1` (the frozen
store's part of a snapshot's observation) is gone: `mvccImage_snapshot.law_holds` is proved.
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

/-- **(Placeholder, false in general.)** The lock's slot moved to a new log and compaction
revision without the client's half of the view. M1-REPLACE: `KV.Put`/`KV.DeleteRange`/
`Txn.End.contract`'s bump (the client's update) and `KV.Compact.contract`. -/
theorem slotX_step_M1 {γ : StoreNames} {q : Qp} {L : Log} {c : Int} (L' : Log) (c' : Int) :
    slotX (GF := GF) γ q L c ⊢ slotX γ q L' c' := by
  sorry -- M1-REPLACE: Txn.End.contract (bump), KV.Compact.contract

/-- **(Placeholder, false in general.)** The writer's slot moved to the committed log without the
client's half of the view. M1-REPLACE: `Txn.End.contract`'s bump. -/
theorem slotY_step_M1 {γ : StoreNames} {L : Log} (L' : Log) : slotY (GF := GF) γ L ⊢ slotY γ L' := by
  sorry -- M1-REPLACE: Txn.End.contract (bump)

/-- **(Placeholder, false in general.)** The frozen state excluded without a share of the token.
M1-REPLACE: `KV.Write.contract`, `Txn.End.contract` (the writer's backend share,
`mvccBackend γ q`, excludes it: `slotF_share_excl`). -/
theorem slotF_excl_M1 (γ : StoreNames) : slotF (GF := GF) γ ∗ iprop(emp) ⊢ False := by
  sorry -- M1-REPLACE: KV.Write.contract, Txn.End.contract (the backend share)

/-- **(Placeholder, false in general.)** The registration lent to a snapshot's freezer excluded by
`updateCompactRev`'s session (`compactLend_sched`) without the means to. (The job's is gone: its
premise `storeRegd`, minted by `updateCompactRev`, excludes the loan, `storeRegd_regLent`.)
M1-REPLACE: `KV.Compact.contract` (the compactor's backend share excludes the freezer, which holds
the whole share; the restore's resumed compaction: the restoring state excludes it). -/
theorem regLent_excl_M1 (γ : StoreNames) : iprop(emp) ∗ regLent (GF := GF) γ ⊢ False := by
  sorry -- M1-REPLACE: KV.Compact.contract (the share excludes the freezer's loan), the job's storeRegd

/-- **(Placeholder, false in general.)** `Compact`'s scheduled record at `rev`: the records'
compaction revision moved to `rev` without the writer's half, and `rev` above it and a revision of
the batch lock's log, past `0`. M1-REPLACE: `KV.Compact.contract` (the writer's slot, with the
compactor's share: its compaction revision is `s.revMu`'s, below `rev`, and its log `s.revMu`'s;
`1 ≤ rev` its premise; the restore's resumed compaction: the image's record, `recsPos`). -/
theorem rcvSched_M1 (γ : StoreNames) (L : Log) (c rev : Int) :
    ghostVar (GF := GF) γ.rcv (1 : Qp).half c ⊢
      ⌜1 ≤ rev ∧ c ≤ rev ∧ rev < L.length⌝ ∗ ghostVar γ.rcv (1 : Qp).half rev := by
  sorry -- M1-REPLACE: KV.Compact.contract (the writer's slot moves with the records)

/-- **(Placeholder, false in general.)** A new batch lock's tracked compaction (`NewStore`'s and
`store.Restore`'s), from the halves of the records' compaction revision and of the job's cursor
(at the last job's `jc`) and the lower bounds' authority only. M1-REPLACE: M3's exact open
(`mvccBackendFor_open.law`: the backend's open gives `fkdOwn γ (fkVals D) ∗ dlsOwn γ ∅`, `fkCl`),
the image's cut (`imageOk`'s `ents`), and `NewStore`'s and `Restore`'s order (the values' halves
taken before `restore()`). -/
theorem cmpTrack_new_M1 (γ : StoreNames) (L : Log) (m : Bucket) (rc : CmpRecs) (jc : Int × Rev) :
    ghostVar (GF := GF) γ.rcv (1 : Qp).half rc.crev ∗ ghostVar γ.jc (1 : Qp).half jc ∗
      monoNatAuthOwn γ.rcl 1 (crevN rc.crev) ⊢ cmpTrack γ L m rc := by
  sorry -- M1-REPLACE: M3's exact open, the image's cut (NewStore, store.Restore)

end placeholders

section placeholdersW
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **(Placeholder, false in general.)** The watchable store's lock's slot made from nothing (today's
`NewStore` returns none of the pending revision's parts). M1-REPLACE: `New.spec` (the watchable
store's constructor gives its lock the quarter). -/
theorem wsSlot_make_M1 (γ : WsNames) (L : Log) : ⊢ wsSlot (GF := GF) γ 1 L := by
  sorry -- M1-REPLACE: New.spec

/-- **(Placeholder, false in general.)** The watchable store's lock's slot moved to a new notified
log without the client's update. M1-REPLACE: `Txn.End.contract`'s notify step, `KV.Restore.contract`. -/
theorem wsSlot_step_M1 {γ : WsNames} {q : Qp} {L : Log} (L' : Log) :
    wsSlot (GF := GF) γ q L ⊢ wsSlot γ q L' := by
  sorry -- M1-REPLACE: Txn.End.contract (notify), KV.Restore.contract

end placeholdersW

end mvcc
end EtcdGrove
end Perennial
