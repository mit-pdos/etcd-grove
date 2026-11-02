/-
**What `cachekv`'s check of the cache's `Get` relies on** (pure; 2026-11-02): the state at a
revision `n` of a log whose revisions are each empty or one put is, key by key, the last put at or
below `n` (`stateAt_lastPut`), and with a watch's events gap-free from revision `2` (`collect`'s,
the puts at revisions `2, 3, ...` of the log), that is the last event of the key at or below `n`
(`lastPut_of_events`): what `checkGet` compares the cache's answer with (`CheckGetOk`).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- A change's put value of the key `k` (none for another key or a delete). -/
def putOf (k : GoString) : mvcc.Change → Option GoString
  | .put k' v _ => if k' = k then some v else none
  | .del _ => none

/-- **The last put of `k` in the revisions `0 … n` of `L`.** -/
def lastPut (L : mvcc.Log) (k : GoString) (n : Nat) : Option GoString :=
  ((L.take (n + 1)).flatten.filterMap (putOf k)).getLast?

/-- A log of revisions each empty or one put, of no lease. -/
def OnePuts (L : mvcc.Log) : Prop :=
  ∀ cs ∈ L, cs = [] ∨ ∃ (k v : GoString), cs = [mvcc.Change.put k v (W64 0)]

theorem lastPut_succ (L : mvcc.Log) (k : GoString) (n : Nat) (h : n + 1 < L.length) :
    lastPut L k (n + 1) = (L[n + 1].filterMap (putOf k)).getLast?.or (lastPut L k n) := by
  unfold lastPut
  rw [List.take_add_one (i := n + 1), List.getElem?_eq_getElem h, Option.toList_some,
    List.flatten_append, List.filterMap_append, List.flatten_singleton, List.getLast?_append]

/-- One revision's step, at a key: an empty revision keeps its value, a put of it sets it. -/
theorem findKey_one (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (r : w64)
    (k : GoString) (cs : List mvcc.Change)
    (hc : cs = [] ∨ ∃ (k' v : GoString), cs = [mvcc.Change.put k' v (W64 0)]) :
    (mvcc.findKey k (mvcc.applyChanges r s cs)).map EtcdKv.value =
      (cs.filterMap (putOf k)).getLast?.or ((mvcc.findKey k s).map EtcdKv.value) := by
  rcases hc with rfl | ⟨k', v, rfl⟩
  · simp [mvcc.applyChanges, Option.or]
  · simp only [mvcc.applyChanges, List.foldl_cons, List.foldl_nil, mvcc.applyChange,
      List.filterMap_cons, List.filterMap_nil, putOf]
    by_cases hk : k' = k
    · subst hk
      obtain ⟨nv, hnv, -⟩ := mvcc.findKey_putKv_self hs r k' v (W64 0)
      have hval : nv.value = v := by
        unfold putKv at hnv
        simp only at hnv
        rw [mvcc.findKey_btInsert _ s hs] at hnv
        cases h : mvcc.findKey k' s with
        | none =>
          unfold mvcc.findKey at h
          simp only [h] at hnv
          simp at hnv
          rw [← hnv]
        | some kv =>
          unfold mvcc.findKey at h
          simp only [h] at hnv
          have hk : kv.key = k' := by simpa using List.find?_some h
          simp [hk] at hnv
          rw [← hnv]
      rw [hnv]; simp [hval, Option.or]
    · rw [mvcc.findKey_putKv_other hs r k k' v (W64 0) hk]
      simp [hk, Option.or]

/-- **The state at `n` of a log of single puts, at a key, is its last put at or below `n`.** -/
theorem stateAt_lastPut (L : mvcc.Log) (hL : OnePuts L) (k : GoString) :
    ∀ n, n < L.length → (mvcc.findKey k (mvcc.stateAt L n)).map EtcdKv.value = lastPut L k n
  | 0, h0 => by
    rw [txn.stateAt_zero L h0, findKey_one [] List.Pairwise.nil _ k _
      (hL _ (List.getElem_mem h0))]
    unfold lastPut
    rw [List.take_one, List.head?_eq_getElem? , List.getElem?_eq_getElem h0]
    simp [mvcc.findKey, Option.or]
    cases List.findSome? (putOf k) L[0].reverse <;> rfl
  | n + 1, h => by
    rw [txn.stateAt_succ L n h, findKey_one _ (mvcc.stateAt_sorted L n) _ k _
      (hL _ (List.getElem_mem h)), stateAt_lastPut L hL k n (by omega), lastPut_succ L k n h]

/-- **What `lastVal(evs, k, r)` returns**: the value of the last event of `k` at or below `r`. -/
def lastValL (evs : List common.wev) (k : GoString) (r : w64) : Option GoString :=
  ((evs.filter (fun e => decide (sint.Z e.Rev' ≤ sint.Z r ∧ e.Key' = k))).getLast?).map
    (fun e => e.Val')

/-- One event more. -/
theorem lastValL_snoc (evs : List common.wev) (e : common.wev) (k : GoString) (r : w64) :
    lastValL (evs ++ [e]) k r =
      if sint.Z e.Rev' ≤ sint.Z r ∧ e.Key' = k then some e.Val' else lastValL evs k r := by
  unfold lastValL
  rw [List.filter_append]
  by_cases h : sint.Z e.Rev' ≤ sint.Z r ∧ e.Key' = k
  · simp [h]
  · simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, h, ↓reduceIte,
      List.append_nil]

/-- **What `checkGet(evs, r, kvs)` checks** of the answer's key-values `s`: each one's value its
key's last event's at or below `r`, and each key with an event at or below `r` among them. -/
def CheckGetOk (evs : List common.wev) (r : w64) (s : List EtcdKv) : Prop :=
  (∀ kv ∈ s, lastValL evs kv.key r = some kv.value) ∧
  ∀ e ∈ evs, sint.Z e.Rev' ≤ sint.Z r → ∃ kv ∈ s, kv.key = e.Key'

/-- Events at revisions `o, o + 1, ...`: the ones at or below `r` are the first `r + 1 - o`. -/
theorem filter_revs (p : common.wev → Bool) (r : Int) :
    ∀ (evs : List common.wev) (o : Int), 0 ≤ o →
      (∀ (i : Nat) (e : common.wev), evs[i]? = some e → sint.Z e.Rev' = o + i) →
      evs.filter (fun e => decide (sint.Z e.Rev' ≤ r) && p e) =
        (evs.take (r + 1 - o).toNat).filter p
  | [], _, _, _ => by simp
  | e :: es, o, ho, h => by
    have h0 : sint.Z e.Rev' = o := by simpa using h 0 e rfl
    have ih := filter_revs p r es (o + 1) (by omega)
      (fun i e' he => by have := h (i + 1) e' (by simpa using he); push_cast at this; omega)
    by_cases hr : sint.Z e.Rev' ≤ r
    · have hk : (r + 1 - o).toNat = (r + 1 - (o + 1)).toNat + 1 := by omega
      rw [hk, List.take_succ_cons, List.filter_cons, List.filter_cons, ih]
      simp [hr]
    · have hk : (r + 1 - o).toNat = 0 := by omega
      have hk' : (r + 1 - (o + 1)).toNat = 0 := by omega
      rw [hk, List.filter_cons, ih, hk']
      simp [hr]

/-- **The log's last put is the events' last** (a log whose revisions `0` and `1` are empty and
whose revision `2 + i` is the put of the event `i`). -/
theorem lastPut_of_events (L : mvcc.Log) (evs : List common.wev) (k : GoString)
    (h0 : ∀ j cs, j < 2 → L[j]? = some cs → cs = [])
    (he : ∀ (i : Nat) (e : common.wev), evs[i]? = some e →
      L[2 + i]? = some [mvcc.Change.put e.Key' e.Val' (W64 0)]) :
    ∀ n, 1 ≤ n → n < L.length → n ≤ 1 + evs.length →
      lastPut L k n = (((evs.take (n - 1)).filter (fun e => decide (e.Key' = k))).getLast?).map
        (fun e => e.Val')
  | 0, h1, _, _ => absurd h1 (by decide)
  | 1, _, hl, _ => by
    have hL0 : L[0]? = some [] := by
      have := List.getElem?_eq_getElem (l := L) (i := 0) (by omega)
      rw [this, h0 0 _ (by omega) this]
    have hL1 : L[1]? = some [] := by
      have := List.getElem?_eq_getElem (l := L) (i := 1) (by omega)
      rw [this, h0 1 _ (by omega) this]
    unfold lastPut
    rw [List.take_add_one, List.take_one, List.head?_eq_getElem?, hL0, hL1]
    simp
  | n + 2, _, hl, hn => by
    rw [lastPut_succ L k (n + 1) hl,
      lastPut_of_events L evs k h0 he (n + 1) (by omega) (by omega) (by omega)]
    have hi : n < evs.length := by omega
    have hev := he n evs[n] (List.getElem?_eq_getElem hi)
    rw [show 2 + n = n + 2 by omega, List.getElem?_eq_getElem hl] at hev
    simp only [Option.some.injEq] at hev
    rw [hev, show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega,
      List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.filter_append,
      List.getLast?_append]
    simp only [List.filterMap_cons, List.filterMap_nil, putOf, List.filter_cons, List.filter_nil]
    by_cases hk : evs[n].Key' = k <;> simp [hk, Option.or]

/-- **The check passes on the state at `r`**: with a log of single puts whose revisions `0` and `1`
are empty and whose revision `2 + i` is the event `i`'s put, the events (each under `pfx`)
gap-free up to `r`, the state at `r` under `pfx` is what `checkGet` accepts. -/
theorem checkGetOk_of (L : mvcc.Log) (evs : List common.wev) (r : w64) (pfx : GoString)
    (hL : OnePuts L) (h0 : ∀ j cs, j < 2 → L[j]? = some cs → cs = [])
    (he : ∀ (i : Nat) (e : common.wev), evs[i]? = some e →
      L[2 + i]? = some [mvcc.Change.put e.Key' e.Val' (W64 0)] ∧ sint.Z e.Rev' = 2 + i)
    (hpfx : ∀ e ∈ evs, pfx <+: e.Key')
    (hr1 : 1 ≤ sint.Z r) (hrL : sint.Z r < L.length) (hre : sint.Z r ≤ 1 + evs.length) :
    CheckGetOk evs r (txn.underPfx pfx (mvcc.stateAt L (sint.Z r).toNat)) := by
  have hlv : ∀ k, lastValL evs k r = lastPut L k (sint.Z r).toNat := by
    intro k
    unfold lastValL
    have hf := filter_revs (fun e => decide (e.Key' = k)) (sint.Z r) evs 2 (by omega)
      (fun i e h => (he i e h).2)
    simp only [Bool.decide_and] at hf ⊢
    rw [hf, lastPut_of_events L evs k h0 (fun i e h => (he i e h).1) (sint.Z r).toNat
      (by omega) (by omega) (by omega)]
    rw [show (sint.Z r + 1 - 2).toNat = (sint.Z r).toNat - 1 by omega]
  refine ⟨fun kv hkv => ?_, fun e hev hle => ?_⟩
  · have hm := (txn.mem_underPfx.1 hkv).1
    have hf := txn.findKey_of_mem_sorted (mvcc.stateAt_sorted L _) hm
    have := stateAt_lastPut L hL kv.key (sint.Z r).toNat (by omega)
    rw [hf] at this
    rw [hlv, ← this]; rfl
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hev
    have hri := (he i e hi).2
    have hsome : (lastPut L e.Key' (sint.Z r).toNat).isSome := by
      rw [← hlv]
      unfold lastValL
      simp only [Option.isSome_map]
      rw [List.getLast?_isSome, ← List.length_pos_iff, List.length_pos_iff_exists_mem]
      exact ⟨e, List.mem_filter.2 ⟨hev, by simp [hle]⟩⟩
    rw [← stateAt_lastPut L hL e.Key' (sint.Z r).toNat (by omega), Option.isSome_map] at hsome
    obtain ⟨kv, hkv⟩ := Option.isSome_iff_exists.1 hsome
    have hkk : kv.key = e.Key' := by
      have := List.find?_some hkv; simpa using this
    refine ⟨kv, txn.mem_underPfx.2 ⟨mvcc.findKey_mem hkv, by rw [hkk]; exact hpfx e hev⟩, hkk⟩

end pure

end cachekv
end EtcdGrove
end Perennial
