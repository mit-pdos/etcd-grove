/-
**watchkv's watch events, read from the KV state** (2026-10-26). Lean-first (no Rocq
counterpart). Pure.

The client's Watch spec says a response's events are the KV state's (`σ.rangeEvents o (c+1)
(c'+1)`, `client/v3/WatchStateDefs.lean`). For a state of a watchkv log (`WkLog P σ.log`: revisions
`0` and `1` empty, every later one one put of the plan), well formed through the revision `r` the
response reaches (`kvLogOkTo σ r`):

* `revEvents_plan`: a revision `m` in `[2, r]` has one event, the put of its plan pair
  (`σ.log[m] = [put k v 0]`): not a delete (the key's create revision is positive:
  `txn.stateAt_client_revs` at the log's prefix through `r`), its key-value the key, `v` and
  modified at `m`;
* `rangeEvents_plan`: the prefix watch's events of the revisions `[lo, hi)` (`lo ≥ 1`,
  `hi ≤ r + 1`) are those revisions' from `2` on, one each (`planEv σ m`), every plan key being
  under the prefix.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLogOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ClientLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Workload

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

theorem flatten_map_single {α β : Type _} (l : List α) (f : α → β) :
    (l.map fun a => [f a]).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]

/-- **Revision `m`'s event** (its first; for a plan revision, its only one). -/
def planEv (σ : KVState) (m : Nat) : mvcc.EvM :=
  ((σ.revEvents m)[0]?).getD ⟨false, ⟨[], W64 0, W64 0, W64 0, [], W64 0⟩, none⟩

/-- A key found is in the state. -/
theorem findKey_mem {k : GoString} {s : List EtcdKv} {v : EtcdKv} (h : mvcc.findKey k s = some v) :
    v ∈ s := by
  unfold mvcc.findKey at h
  exact List.mem_of_find?_eq_some h

/-- **A plan revision's one event** (see the file header). -/
theorem revEvents_plan (P : List (GoString × GoString)) (σ : KVState) (r : Nat)
    (hW : WkLog P σ.log) (hok : kvLogOkTo σ r) (m : Nat) (h2 : 2 ≤ m) (hm : m ≤ r) :
    ∃ (k v : GoString) (nv : EtcdKv), (k, v) ∈ P ∧
      σ.log[m]? = some [mvcc.Change.put k v (W64 0)] ∧
      σ.revEvents m = [⟨false, nv, none⟩] ∧ nv.key = k ∧ nv.value = v ∧ nv.modRev = W64 m := by
  obtain ⟨he, hr, hr63, hwf, hsm, -⟩ := hok
  have hc : σ.compacted = 0 := by rw [he]; rfl
  have hlen : σ.log.length = σ.rev + 1 := by
    simp only [KVState.log, KVState.rev, List.length_cons, hc]; omega
  have hml : m < σ.log.length := by omega
  obtain ⟨cs, hcs⟩ : ∃ cs, σ.log[m]? = some cs := ⟨_, List.getElem?_eq_getElem hml⟩
  obtain ⟨k, v, hkv, rfl⟩ := hW.2 m cs h2 hcs
  -- the state before the revision, sorted, its records created at positive revisions
  have hrev : σ.revEvents m = (kvStateOf σ.log).revEvents m := by rw [← he]
  rw [revEvents_kvStateOf σ.log m (by omega) (by omega)] at hrev
  have hgd : σ.log.getD m [] = [mvcc.Change.put k v (W64 0)] := by
    simp [List.getD, hcs]
  rw [hgd] at hrev
  have hsort := mvcc.stateAt_sorted σ.log (m - 1)
  have hpre : σ.log.take (r + 1) <+: σ.log := List.take_prefix _ _
  have htl : (σ.log.take (r + 1)).length = r + 1 := by rw [List.length_take]; omega
  have hst : mvcc.stateAt (σ.log.take (r + 1)) (m - 1) = mvcc.stateAt σ.log (m - 1) :=
    (txn.stateAt_of_prefix hpre (r := m - 1) (by rw [htl]; omega)).symm
  have hpos : ∀ x ∈ mvcc.stateAt σ.log (m - 1), 0 < sint.Z x.createRev := by
    intro x hx
    rw [← hst] at hx
    exact (txn.stateAt_client_revs _ hwf (by omega) hsm (m - 1) (by omega) x hx).1
  have hm63 : sint.Z (W64 (m : Int)) = m := by word
  -- the put's key-value
  have hput := mvcc.findKey_putKv_self_eq hsort (W64 (m : Int)) k v (W64 0)
  have hevs : ∀ nv, mvcc.findKey k (putKv (W64 (m : Int)) k v (W64 0)
      (mvcc.stateAt σ.log (m - 1))) = some nv → 0 < sint.Z nv.createRev →
      σ.revEvents m = [⟨false, nv, none⟩] := by
    intro nv hnv hc0
    rw [hrev]
    unfold mvcc.evsOfRevM mvcc.changeKv
    simp only [List.length_singleton, List.range_one, List.filterMap_cons, List.filterMap_nil,
      List.getElem?_cons_zero, Nat.zero_add, List.take_succ_cons, List.take_zero]
    unfold mvcc.applyChanges
    simp only [List.foldl_cons, List.foldl_nil, mvcc.applyChange]
    rw [hnv]
    simp only [Option.map_some]
    unfold mvcc.evOfKv
    rw [if_neg (by intro h0; rw [h0] at hc0; simp at hc0)]
  cases hfk : mvcc.findKey k (mvcc.stateAt σ.log (m - 1)) with
  | some old =>
    rw [hfk] at hput
    have hold := hpos old (findKey_mem hfk)
    refine ⟨k, v, _, hkv, hcs, hevs _ hput hold, ?_, ?_, ?_⟩
    · exact (show old.key = k from mvcc.findKey_key hfk)
    · rfl
    · rfl
  | none =>
    rw [hfk] at hput
    refine ⟨k, v, _, hkv, hcs, hevs _ hput ?_, ?_, ?_, ?_⟩
    · simp only; omega
    all_goals rfl

/-- **A prefix watch's events of the revisions `[lo, hi)`, from the state** (see the file
header). -/
theorem rangeEvents_plan (P : List (GoString × GoString)) (pfx : GoString) (o : OpFull)
    (hrange : ∀ k, inRange o.key o.base.rangeEnd k = true ↔ pfx <+: k)
    (hpk : ∀ kv ∈ P, pfx <+: kv.1) (σ : KVState) (r : Nat)
    (hW : WkLog P σ.log) (hok : kvLogOkTo σ r) (lo hi : Nat) (hlo : 1 ≤ lo) (hhi : hi ≤ r + 1) :
    σ.rangeEvents o lo hi = (List.range' (max lo 2) (hi - max lo 2)).map (planEv σ) := by
  have hc : σ.compacted = 0 := by rw [hok.1]; rfl
  have hlen : σ.log.length = σ.rev + 1 := by
    simp only [KVState.log, KVState.rev, List.length_cons, hc]; omega
  -- revision `1` has no event
  have h1 : σ.revEvents 1 = [] := by
    have hrev : σ.revEvents 1 = (kvStateOf σ.log).revEvents 1 := by rw [← hok.1]
    by_cases hl : 1 ≤ σ.log.length - 1
    · rw [revEvents_kvStateOf σ.log 1 (by omega) hl] at hrev
      obtain ⟨cs, hcs⟩ : ∃ cs, σ.log[1]? = some cs := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have := hW.1 1 cs (by omega) hcs
      subst this
      have hgd : σ.log.getD 1 [] = [] := by simp [List.getD, hcs]
      rw [hrev, hgd]
      simp [mvcc.evsOfRevM]
    · unfold KVState.revEvents
      have : σ.changesAt 1 = [] := by
        unfold KVState.changesAt
        simp only [hc]
        split
        · rfl
        · simp only [KVState.log, List.length_cons] at hl
          have : σ.changes = [] := List.eq_nil_of_length_eq_zero (by omega)
          simp [this]
      rw [this]; simp [mvcc.evsOfRevM]
  -- revisions from `2` on: one event each, under the prefix
  have hm : ∀ m, 2 ≤ m → m < hi →
      σ.revEvents m = [planEv σ m] ∧ inRange o.key o.base.rangeEnd (planEv σ m).kv.key = true := by
    intro m h2 hmh
    obtain ⟨k, v, nv, hkv, -, hev, hk, -, -⟩ := revEvents_plan P σ r hW hok m h2 (by omega)
    have hp : planEv σ m = ⟨false, nv, none⟩ := by unfold planEv; rw [hev]; rfl
    rw [hp, hev]
    refine ⟨rfl, (hrange _).2 ?_⟩
    simp only [hk]; exact hpk (k, v) hkv
  unfold KVState.rangeEvents
  -- split off revision `1`
  have hsplit : (List.range' lo (hi - lo)).map σ.revEvents =
      (if lo = 1 ∧ 1 < hi then [σ.revEvents 1] else []) ++
        (List.range' (max lo 2) (hi - max lo 2)).map σ.revEvents := by
    by_cases hl1 : lo = 1
    · subst hl1
      by_cases hh : 1 < hi
      · simp only [hh, and_self, ↓reduceIte, List.singleton_append]
        rw [show hi - 1 = (hi - 2) + 1 by omega, List.range'_succ, List.map_cons]
        simp
      · simp only [hh, and_false, ↓reduceIte, List.nil_append]
        rw [show hi - 1 = 0 by omega, show hi - max 1 2 = 0 by omega]; rfl
    · simp only [hl1, false_and, ↓reduceIte, List.nil_append]
      rw [show max lo 2 = lo by omega]
  rw [hsplit]
  have hmap : (List.range' (max lo 2) (hi - max lo 2)).map σ.revEvents =
      (List.range' (max lo 2) (hi - max lo 2)).map (fun m => [planEv σ m]) := by
    apply List.map_congr_left
    intro m hmem
    rw [List.mem_range'] at hmem
    exact (hm m (by omega) (by omega)).1
  rw [hmap]
  have hfl : ((if lo = 1 ∧ 1 < hi then [σ.revEvents 1] else []) ++
      (List.range' (max lo 2) (hi - max lo 2)).map (fun m => [planEv σ m])).flatten =
      (List.range' (max lo 2) (hi - max lo 2)).map (planEv σ) := by
    rw [List.flatten_append]
    have he : (if lo = 1 ∧ 1 < hi then [σ.revEvents 1] else []).flatten = [] := by
      split <;> simp [h1]
    rw [he, List.nil_append]
    exact flatten_map_single _ _
  rw [hfl]
  apply List.filter_eq_self.2
  intro ev hev
  obtain ⟨m, hmem, rfl⟩ := List.mem_map.1 hev
  rw [List.mem_range'] at hmem
  exact (hm m (by omega) (by omega)).2

end pure

end watchkv
end EtcdGrove
end Perennial
