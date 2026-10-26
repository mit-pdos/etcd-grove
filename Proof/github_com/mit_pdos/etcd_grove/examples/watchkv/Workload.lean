/-
**watchkv's workload** (D23, 2026-10-20). Lean-first (no Rocq counterpart).

Until D45 (2026-10-25) the server's workload parameter restricted the log to the plan's puts;
now the plan is watchkv's own fact, kept with the KV state's changes in the adapter's invariant
(`client.kmInv` at `γ.W = wkW P`): every change is a writer's put of the plan `P` (`wkW_put`). Its
pure part: a watchkv log (`WkLog`: revisions `0` and `1` empty, every later one exactly one put of
the plan), which gives `NoDupKeysPerRev` (`WkLog.noDup`), and `wkW P l`, the fact about the state's
changes `l` (the log `[] :: l` a watchkv log).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open go_etcd_io.etcd.server.v3.etcdserver

/-- A revision of a watchkv log from `2` on: one put of the plan, no lease. -/
def wkRev (P : List (GoString × GoString)) (cs : List mvcc.Change) : Prop :=
  ∃ k v, (k, v) ∈ P ∧ cs = [.put k v (W64 0)]

/-- **A watchkv log**: its first two revisions empty, every later one a put of the plan. -/
def WkLog (P : List (GoString × GoString)) (L : mvcc.Log) : Prop :=
  (∀ j cs, j < 2 → L[j]? = some cs → cs = []) ∧ ∀ j cs, 2 ≤ j → L[j]? = some cs → wkRev P cs

theorem WkLog.prefix {P : List (GoString × GoString)} {L L' : mvcc.Log} (h : WkLog P L)
    (hp : L' <+: L) : WkLog P L' := by
  obtain ⟨r, rfl⟩ := hp
  refine ⟨fun j cs hj hc => h.1 j cs hj ?_, fun j cs hj hc => h.2 j cs hj ?_⟩ <;>
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hc).1] <;> exact hc

/-- The start log is a watchkv log. -/
theorem WkLog.start (P : List (GoString × GoString)) : WkLog P [[], []] := by
  refine ⟨fun j cs _ h => ?_, fun j cs hj h => ?_⟩
  · rcases j with _ | _ | j <;> simp at h <;> exact h
  · rcases j with _ | _ | j
    · omega
    · omega
    · simp at h

/-- A short log's revisions are empty when it is a prefix of the start log. -/
theorem WkLog.of_start_prefix (P : List (GoString × GoString)) {L : mvcc.Log}
    (h : L <+: [[], []]) : WkLog P L := (WkLog.start P).prefix h

/-- One revision more. -/
theorem WkLog.snoc {P : List (GoString × GoString)} {L : mvcc.Log} {cs : List mvcc.Change}
    (h : WkLog P L) (hl : 2 ≤ L.length) (hc : wkRev P cs) : WkLog P (L ++ [cs]) := by
  refine ⟨fun j c hj hj' => h.1 j c hj ?_, fun j c hj hj' => ?_⟩
  · rw [List.getElem?_append_left (by omega)] at hj'; exact hj'
  · rcases Nat.lt_or_ge j L.length with hjl | hjl
    · rw [List.getElem?_append_left hjl] at hj'; exact h.2 j c hj hj'
    · rw [List.getElem?_append_right hjl] at hj'
      have : j - L.length = 0 := by
        have := (List.getElem?_eq_some_iff.mp hj').1; simp at this; omega
      rw [this] at hj'; simp at hj'; subst hj'; exact hc

/-- **A watchkv log writes each key once per revision.** -/
theorem WkLog.noDup {P : List (GoString × GoString)} {L : mvcc.Log} (h : WkLog P L) :
    txn.NoDupKeysPerRev L := by
  intro cs hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hcs
  rcases Nat.lt_or_ge j 2 with h2 | h2
  · rw [h.1 j cs h2 hj]; simp
  · obtain ⟨k, v, -, rfl⟩ := h.2 j cs h2 hj
    simp

/-- **The plan's fact about the KV state's changes** (the adapter's `γ.W`, `client.KMNames`): the
log of the changes is a watchkv log, and the changes hold revision `1`'s (so a put appends a
revision from `2` on). -/
def wkW (P : List (GoString × GoString)) (l : List (List mvcc.Change)) : Prop :=
  WkLog P ([] :: l) ∧ l ≠ []

/-- The start state's changes (`kvStateOf [[], []]`'s, revision `1` empty). -/
theorem wkW_start (P : List (GoString × GoString)) : wkW P [[]] :=
  ⟨WkLog.start P, by simp⟩

/-- The put of `k ↦ v` with no options, a put of the plan, keeps the fact. -/
theorem wkW_put (P : List (GoString × GoString)) (k v : GoString) (h : (k, v) ∈ P)
    (σ : KVState) (hW : wkW P σ.changes) :
    wkW P (kvOpStep (.put (txn.putOpOf k v (W64 0) false false false)) σ).changes := by
  have hnp : txn.needsPrev (txn.putOpOf k v (W64 0) false false false) = false := by
    simp [txn.needsPrev, txn.putOpOf]
  have hlm : ¬ σ.leaseMissing (txn.putOpOf k v (W64 0) false false false).leaseID := by
    simp [txn.putOpOf, KVState.leaseMissing]
  simp only [kvOpStep, hlm, hnp, Bool.false_and, Bool.false_eq_true, ↓reduceIte, KVState.commit,
    List.cons_ne_nil]
  refine ⟨?_, by simp⟩
  have hc : txn.putChangeOf (txn.putOpOf k v (W64 0) false false false)
      (mvcc.findKey k σ.kvs) = .put k v (W64 0) := by
    simp [txn.putChangeOf, txn.putValOf, txn.putLeaseOf, txn.putOpOf]
  have hl : 2 ≤ ([] :: σ.changes : mvcc.Log).length := by
    have := List.length_pos_iff.2 hW.2; simp; omega
  have := hW.1.snoc hl (cs := [txn.putChangeOf (txn.putOpOf k v (W64 0) false false false)
      (mvcc.findKey (txn.putOpOf k v (W64 0) false false false).key σ.kvs)])
    ⟨k, v, h, by simp [txn.putOpOf] at hc ⊢; exact hc⟩
  simpa using this

/-- A prefix of the changes the fact holds of is a prefix of a watchkv log. -/
theorem wkW_prefix {P : List (GoString × GoString)} {l l' : List (List mvcc.Change)}
    (hW : wkW P l') (hp : l <+: l') {L : mvcc.Log} (hL : L <+: [] :: l) : WkLog P L :=
  hW.1.prefix (hL.trans (List.prefix_cons_inj _ |>.2 hp))

end watchkv
end EtcdGrove
end Perennial
