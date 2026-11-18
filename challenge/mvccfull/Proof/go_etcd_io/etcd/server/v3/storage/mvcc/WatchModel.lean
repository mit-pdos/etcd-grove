/-
**The watchers' events of the log** (pure; moved from `InvWatchStore.lean`, 2026-11-05, so that the
API's pure part, `ApiState`, and the stream's history, `Api/StreamLog.lean`, come before the
channel invariant, which keeps the stream's history: `notes/mvcc-api-invariants.md`, "Hand-off:
stage 2, the watch chain"). The events the watchers see of a revision `r` (`evsOfRevM`) are the
key-values its changes wrote (`changeKv`), made events as `End` does (`evOfKv`); `watchEvents log r
lo hi` are the events of the revisions `[lo, hi)` of `log` whose key the range `r` holds, in revision
order; `filtered fs evs` keeps the events no filter predicate of `fs` drops.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchBatch
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchGroup

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The watchers' events of the log (pure) -/

/-- The event `End` makes of a change's key-value at revision `r`: a create revision `0` (the
key alone, a delete's `changeKv`) is a `DELETE` with `ModRevision := r`, else a `PUT`; no
previous key-value. -/
def evOfKv (r : Nat) (kv : EtcdKv) : EvM :=
  if kv.createRev = W64 0 then ⟨true, { kv with modRev := W64 r }, none⟩ else ⟨false, kv, none⟩

/-- The events of revision `r` (changes `cs`, the state `before` before them), in order. -/
def evsOfRevM (r : Nat) (before : List EtcdKv) (cs : List Change) : List EvM :=
  (List.range cs.length).filterMap fun i => (changeKv (W64 r) before cs i).map (evOfKv r)

/-- The events of the revisions `[lo, hi)` of `log`, in revision order. -/
def logEvents (log : Log) (lo hi : Nat) : List EvM :=
  ((List.range' lo (hi - lo)).map fun m =>
    evsOfRevM m (stateAt log (m - 1)) (log.getD m [])).flatten

/-- The range's events of `log` at the revisions `[lo, hi)`, in revision order. -/
def watchEvents (log : Log) (r : WatchRange) (lo hi : Nat) : List EvM :=
  (logEvents log lo hi).filter fun ev => r.covers ev.kv.key

/-- The events no filter predicate of `fs` drops (`watcher.send`'s loop). -/
def filtered (fs : List (EvM → Bool)) (evs : List EvM) : List EvM :=
  evs.filter fun ev => fs.all fun p => !(p ev)

/-! ## Countability (for the ghost state) -/

instance etcdKvCountableW : Pos.Countable EtcdKv :=
  .ofInjective (fun k => Pos.Countable.encode (k.key, k.createRev, k.modRev, k.version, k.value, k.lease))
    (by rintro ⟨a, b, c, d, e, f⟩ ⟨a', b', c', d', e', f'⟩ h; have h := Pos.encode_inj h; simp_all)

instance EvM.countable : Pos.Countable EvM :=
  .ofInjective (fun e => Pos.Countable.encode (e.del, e.kv, e.prevKv))
    (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h; have h := Pos.encode_inj h; simp_all)

instance WatchRange.countable : Pos.Countable WatchRange :=
  .ofInjective (fun r => Pos.Countable.encode (r.key, r.end?, r.startRev, r.id))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- A response the store sent on a stream's channel: the watcher it was sent for (ghost), its
`WatchID`, events and `Revision`; and (ghost, unit W-K) the watchers a progress response covers
(`cov`: `respCov`; empty for any other response) and, for one of id `-1`, the watchers registered
on the channel when it was sent (`regs`); and its position in the sent list (`idx`). -/
structure RespM where
  w : Loc
  id : w64
  evs : List EvM
  rev : w64
  cov : List Loc
  regs : List Loc
  /-- its position in the channel's sent list (ghost, K1b): so the responses sent are distinct -/
  idx : Nat
  /-- (watches across a compaction, 2026-11-01) its `CompactRevision`: `0`, or the store's
  compaction revision when the watcher's next revision was compacted (`chooseAll`'s response) -/
  compactRev : w64 := W64 0

instance RespM.countable : Pos.Countable RespM :=
  .ofInjective (fun r => Pos.Countable.encode (r.w, r.id, r.evs, r.rev, r.cov, r.regs, r.idx,
      r.compactRev))
    (by rintro ⟨a, b, c, d, e, f, g, i⟩ ⟨a', b', c', d', e', f', g', i'⟩ h; have h := Pos.encode_inj h;
        simp_all)

end mvcc
end EtcdGrove
end Perennial
