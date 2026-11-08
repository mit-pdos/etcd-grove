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

theorem logEvents_empty (log : Log) {lo hi : Nat} (h : hi ≤ lo) : logEvents log lo hi = [] := by
  unfold logEvents; rw [show hi - lo = 0 by omega]; rfl

theorem watchEvents_empty (log : Log) (r : WatchRange) {lo hi : Nat} (h : hi ≤ lo) :
    watchEvents log r lo hi = [] := by
  unfold watchEvents; rw [logEvents_empty log h]; rfl

theorem logEvents_append (log : Log) {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    logEvents log lo hi = logEvents log lo mid ++ logEvents log mid hi := by
  unfold logEvents
  rw [← List.flatten_append, ← List.map_append]
  congr 2
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, ← List.range'_append_1,
    show lo + (mid - lo) = mid by omega]

theorem watchEvents_append (log : Log) (r : WatchRange) {lo mid hi : Nat} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) :
    watchEvents log r lo hi = watchEvents log r lo mid ++ watchEvents log r mid hi := by
  unfold watchEvents; rw [logEvents_append log h1 h2, List.filter_append]

theorem logEvents_succ (log : Log) (m : Nat) :
    logEvents log m (m + 1) = evsOfRevM m (stateAt log (m - 1)) (log.getD m []) := by
  unfold logEvents
  rw [show m + 1 - m = 1 by omega]
  simp

/-- The events of a log at revisions below a prefix's length are the prefix's. -/
theorem logEvents_prefix {L L' : Log} (hp : L <+: L') {lo hi : Nat} (hhi : hi ≤ L.length) :
    logEvents L lo hi = logEvents L' lo hi := by
  unfold logEvents
  congr 1
  apply List.map_congr_left
  intro m hm
  rw [List.mem_range'] at hm
  have hm' : m < L.length := by omega
  obtain ⟨T, rfl⟩ := hp
  have hs : stateAt (L ++ T) (m - 1) = stateAt L (m - 1) := by
    unfold stateAt
    rw [List.take_append_of_le_length (by omega)]
  rw [hs]
  congr 1
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hm']

theorem watchEvents_prefix {L L' : Log} (hp : L <+: L') (r : WatchRange) {lo hi : Nat}
    (hhi : hi ≤ L.length) : watchEvents L r lo hi = watchEvents L' r lo hi := by
  unfold watchEvents; rw [logEvents_prefix hp hhi]

/-- Two comparable logs agree on the events of the revisions both have. -/
theorem watchEvents_cmp {L L' : Log} (hc : L <+: L' ∨ L' <+: L) (r : WatchRange) {lo hi : Nat}
    (h : hi ≤ L.length ∨ hi ≤ lo) (h' : hi ≤ L'.length ∨ hi ≤ lo) :
    watchEvents L r lo hi = watchEvents L' r lo hi := by
  by_cases hlo : hi ≤ lo
  · rw [watchEvents_empty _ _ hlo, watchEvents_empty _ _ hlo]
  · have h1 : hi ≤ L.length := h.resolve_right hlo
    have h2 : hi ≤ L'.length := h'.resolve_right hlo
    rcases hc with hc | hc
    · exact watchEvents_prefix hc r h1
    · exact (watchEvents_prefix hc r h2).symm

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
