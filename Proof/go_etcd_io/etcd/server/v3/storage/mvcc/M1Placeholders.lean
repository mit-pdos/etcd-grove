/-
**Placeholders of the M1 migration** (strict M1, 2026-11-04: `notes/decisions.md`, "strict M1, no
scaffold"). Lean-first (no Rocq counterpart).

The store's locks hold the API's ghost state outright (`InvStore`'s slots at `StoreNames.api`).
Today's specs of the methods that move it (`storeTxnWrite.End`, `store.updateCompactRev`,
`store.Write`'s checkout; the watchable store's `End`, `Restore` and constructor) give their callers none of the client's parts, so their proofs cannot
take the API's steps; each such step is one of the lemmas below, **false in general** and proved
by `sorry`, marked `M1-REPLACE` with the API contract whose proof replaces it at stage 2 (the
proofs using them are rewritten against the API's contracts, and this module goes). Nothing new
may use them.
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

/-- **(Placeholder, false in general.)** A response sent on a stream's channel appended to the
stream's history without its send's premises (`api.sent.stepOk`: the response's shape against a
notified-log and a compaction lower bound, its watcher's delivery and registry info by its saved
filters, a `-1` response's coverage and cancelled ids; `api.chanApiAt_send`). Used at the two send
sites (`watcher.send`, `WatchCmpSend`'s `cmp_send_inner`), each of which is to prove them from
today's per-send facts (`respCov`, `covFact`, `respRev`, `respCompl`), the watcher's saved filters
and the senders' lower bounds (the watch chain's item 1, `notes/mvcc-api-invariants.md`).
M1-REPLACE: `wsRecv_ok.law`/`wsChan_recv.law` (the stream's history well formed at every send). -/
theorem chanApi_send_M1 (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (sent recv : List RespM)
    (x : RespM) : chanApi (GF := GF) γ ch γc sent recv ⊢ |==> chanApi γ ch γc (sent ++ [x]) recv := by
  sorry -- M1-REPLACE: wsChan_recv.law, wsRecv_ok.law (a send's stepOk)

end placeholdersW

end mvcc
end EtcdGrove
end Perennial
