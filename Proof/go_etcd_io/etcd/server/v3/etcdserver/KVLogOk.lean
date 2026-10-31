/-
**A KV state is a well-formed log's** (D48, 2026-10-26). Lean-first (no Rocq counterpart).

The client's specs give, with the state `σ` a reply or a watch response reads (the one the
caller's update fired at), that `σ` is the state of a log the store could have made:

* `KVState.log σ`: `σ`'s log, revision `0`'s (no change) then `σ`'s changes;
* `kvLogOkTo σ r`: `σ` is its log's state (`kvStateOf`: nothing compacted, the base the empty
  store), and its log is well formed (`mvcc.LogWf'`: every delete of a present key) and small
  (`txn.LogSmall`: at most `2 ^ 62` changes) through revision `r ≤ σ.rev`, below `2 ^ 63 - 1`,
  and its keys short (`mvcc.LogKeysLe etcdKeyMax`, 2026-10-30: `notes/keylen.md`);
* `kvLogOk σ`: through its current revision (a KV reply's: the log a member applied).

A watch response gives the first only through the revision it moves the stream to: its update
fires at the committed state, whose log the store has not applied yet (and has no bound), while
its events are of a log the store sealed, a prefix of it. The laws of the clients' model of etcd
(`EtcdModel`: positive versions, `createRev ≤ modRev ≤ r`) are facts about such logs
(`txn.stateAt_client_revs`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-! ## Prefixes of well-formed small logs -/

/-- A prefix of a well-formed log is well formed. -/
theorem logWf'_of_append : ∀ {l t : mvcc.Log}, mvcc.LogWf' (l ++ t) → mvcc.LogWf' l
  | _, [], h => by simpa using h
  | l, c :: t, h => by
    have h' : mvcc.LogWf' ((l ++ [c]) ++ t) := by simpa using h
    exact (logWf'_of_append h').prefix

theorem logWf'_of_prefix {l L : mvcc.Log} (hp : l <+: L) (h : mvcc.LogWf' L) : mvcc.LogWf' l := by
  obtain ⟨t, rfl⟩ := hp
  exact logWf'_of_append h

/-- A prefix of a small log is small. -/
theorem logSmall_of_prefix {l L : mvcc.Log} (hp : l <+: L) (h : txn.LogSmall L) : txn.LogSmall l := by
  obtain ⟨t, rfl⟩ := hp
  unfold txn.LogSmall txn.logChanges at *
  simp only [List.map_append, List.sum_append] at h
  omega

/-! ## The definitions -/

/-- **`σ`'s log**: revision `0`'s (no change), then `σ`'s changes. -/
def KVState.log (σ : KVState) : mvcc.Log := [] :: σ.changes

/-- **`σ` is a well-formed small log's state through revision `r`** (see the file header). -/
def kvLogOkTo (σ : KVState) (r : Nat) : Prop :=
  σ = kvStateOf σ.log ∧ r ≤ σ.rev ∧ r + 1 < 2 ^ 63 ∧
    mvcc.LogWf' (σ.log.take (r + 1)) ∧ txn.LogSmall (σ.log.take (r + 1)) ∧
    -- (2026-10-30, `notes/keylen.md`) its keys short
    mvcc.LogKeysLe etcdKeyMax (σ.log.take (r + 1))

/-- **`σ` is a well-formed small log's state** (through its current revision). -/
def kvLogOk (σ : KVState) : Prop := kvLogOkTo σ σ.rev

/-! ## From the server's logs -/

/-- A log whose revision `0` has no change is its state's log. -/
theorem kvStateOf_log (l : mvcc.Log) (h : l[0]? = some []) : (kvStateOf l).log = l := by
  cases l with
  | nil => simp at h
  | cons c l =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [KVState.log, kvStateOf]

/-- **A longer log's state is well formed through a well-formed small log's revisions**: the state
of `C`, through any revision `r` of its prefix `l`. -/
theorem kvLogOkTo_of_prefix {l C : mvcc.Log} (hp : l <+: C) (hw : mvcc.LogWf' l)
    (hs : txn.LogSmall l) (hl : l.length < 2 ^ 63) {r : Nat} (hr : r < l.length)
    (hk : mvcc.LogKeysLe etcdKeyMax l) :
    kvLogOkTo (kvStateOf C) r := by
  have hne : l ≠ [] := by intro h; subst h; simp at hr
  have h0 : C[0]? = some [] := by
    obtain ⟨t, rfl⟩ := hp
    rw [List.getElem?_append_left (List.length_pos_iff.2 hne)]
    exact hw.1 hne
  have hlen : l.length ≤ C.length := hp.length_le
  have ht : C.take (r + 1) = l.take (r + 1) := by
    obtain ⟨t, rfl⟩ := hp; exact List.take_append_of_le_length (by omega)
  have htl : l.take (r + 1) <+: l := List.take_prefix _ _
  refine ⟨by rw [kvStateOf_log C h0], ?_, by omega, ?_, ?_, ?_⟩
  · rw [kvStateOf_rev]; omega
  · rw [kvStateOf_log C h0, ht]; exact logWf'_of_prefix htl hw
  · rw [kvStateOf_log C h0, ht]; exact logSmall_of_prefix htl hs
  · rw [kvStateOf_log C h0, ht]; exact hk.prefix htl

/-- **A well-formed small log's state is well formed.** -/
theorem kvLogOk_of (l : mvcc.Log) (hw : mvcc.LogWf' l) (hs : txn.LogSmall l)
    (hl : l.length < 2 ^ 63) (hne : l ≠ []) (hk : mvcc.LogKeysLe etcdKeyMax l) :
    kvLogOk (kvStateOf l) := by
  unfold kvLogOk
  rw [kvStateOf_rev]
  exact kvLogOkTo_of_prefix (List.prefix_refl l) hw hs hl
    (by have := List.length_pos_iff.2 hne; omega) hk

/-- **A prefix of a well-formed small log's state is well formed** (a write's reply: the log the
write met, the certified log after it extending it). -/
theorem kvLogOk_of_prefix {l C : mvcc.Log} (hp : l <+: C) (hw : mvcc.LogWf' C)
    (hs : txn.LogSmall C) (hl : C.length < 2 ^ 63) (hne : l ≠ [])
    (hk : mvcc.LogKeysLe etcdKeyMax C) : kvLogOk (kvStateOf l) :=
  kvLogOk_of l (logWf'_of_prefix hp hw) (logSmall_of_prefix hp hs)
    (by have := hp.length_le; omega) hne (hk.prefix hp)

/-- Through its current revision, a well-formed state's log is its log. -/
theorem kvLogOk_log {σ : KVState} (h : kvLogOk σ) :
    mvcc.LogWf' σ.log ∧ txn.LogSmall σ.log ∧ σ.log.length < 2 ^ 63 ∧ σ.log.length = σ.rev + 1 := by
  obtain ⟨he, -, hr, hw, hs, -⟩ := h
  have hc : σ.compacted = 0 := by rw [he]; rfl
  have hl : σ.log.length = σ.rev + 1 := by
    simp only [KVState.log, KVState.rev, List.length_cons, hc]; omega
  rw [List.take_of_length_le (by omega)] at hw hs
  exact ⟨hw, hs, by omega, hl⟩

/-- Through its current revision, a well-formed state's log has short keys. -/
theorem kvLogOk_keys {σ : KVState} (h : kvLogOk σ) : mvcc.LogKeysLe etcdKeyMax σ.log := by
  have hl := (kvLogOk_log h).2.2.2
  have hk := h.2.2.2.2.2
  rwa [List.take_of_length_le (by omega)] at hk

end EtcdGrove
end Perennial
