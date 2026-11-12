/-
Pure lemmas for `shared.release` (U2, `notes/bbolt-proof-plan.md`), ported from the old proof's
`old/bbolt/.../internal/freelist/Iface.lean` (over `FLState`, with `uint.Z`; here over `FLPg`,
with `toNat`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

theorem lookup_filter' {V : Type} (m : GMap w64 V) (P : w64 → V → Bool) (k : w64) :
    (GMap.filter P m) !! k = (m !! k).filter (P k) := rfl

/-- Two lists with the same elements up to order sort the same. -/
theorem sortPgids_perm_eq {l1 l2 : List w64} (h : l1.Perm l2) : sortPgids l1 = sortPgids l2 :=
  (sortPgids_eq_of_sorted (sortPgids_sorted l1) ((sortPgids_perm l1).trans h)).symm

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The ids of the entries a filter keeps: those of the map's bindings it keeps. -/
theorem flatIds_filter_perm (m : GMap w64 Pending) (P : w64 → Pending → Bool) :
    (flatIds (GMap.filter P m)).Perm
      ((m.toList.filter (fun kv => P kv.1 kv.2)).flatMap (fun kv => kv.2.ids)) := by
  have h := (toList_perm_of (m := GMap.filter P m) (l := m.toList.filter (fun kv => P kv.1 kv.2))
    ((List.Sublist.map _ List.filter_sublist).nodup (GMap.toList_keys_nodup m))
    (fun k v => by
      rw [List.mem_filter, GMap.mem_toList, lookup_filter']
      cases h : m !! k with
      | none => simp [Option.filter]
      | some w =>
        by_cases hp : P k w = true
        · simp [Option.filter, hp]
          intro e; subst e; exact hp
        · simp [Option.filter, hp]
          intro e; subst e; simpa using hp)).symm
  exact h.flatMap_right _

/-- A map's ids: those of the entries a filter keeps and those it drops. -/
theorem flatIds_filter_split (m : GMap w64 Pending) (P : w64 → Pending → Bool) :
    (flatIds m).Perm (flatIds (GMap.filter P m) ++ flatIds (GMap.filter (fun k v => !P k v) m)) := by
  refine List.Perm.trans ?_ (List.Perm.append (flatIds_filter_perm m _) (flatIds_filter_perm m _)).symm
  rw [← List.flatMap_append]
  exact ((List.filter_append_perm (fun kv : w64 × Pending => P kv.1 kv.2) m.toList).flatMap_right
    _).symm.trans (by simp)

/-- `m` without the keys of `vis` up to `txid` (`release`'s loop, having visited `vis`). -/
def dropUpTo {V : Type} (vis : List w64) (txid : w64) (m : GMap w64 V) : GMap w64 V :=
  GMap.filter (fun k _ => !(decide (k ∈ vis) && decide (k.toNat ≤ txid.toNat))) m

theorem dropUpTo_nil {V : Type} (txid : w64) (m : GMap w64 V) : dropUpTo [] txid m = m := by
  apply GMap.map_eq; intro k
  unfold dropUpTo; rw [lookup_filter']; cases m !! k <;> simp [Option.filter]

theorem dropUpTo_notvis {V : Type} {vis : List w64} {k : w64} (txid : w64) (m : GMap w64 V)
    (h : k ∉ vis) : (dropUpTo vis txid m) !! k = m !! k := by
  unfold dropUpTo; rw [lookup_filter']; cases m !! k <;> simp [Option.filter, h]

theorem dropUpTo_le {V : Type} {vis : List w64} {key txid : w64} (m : GMap w64 V)
    (hle : key.toNat ≤ txid.toNat) :
    dropUpTo (vis ++ [key]) txid m = GMap.delete key (dropUpTo vis txid m) := by
  apply GMap.map_eq; intro k
  unfold dropUpTo; rw [GMap.lookup_delete_iff, lookup_filter', lookup_filter']
  by_cases hk : key = k
  · subst hk; cases m !! key <;> simp [Option.filter, hle]
  · simp only [hk, if_false, List.mem_append, List.mem_singleton, Ne.symm hk, _root_.or_false]

theorem dropUpTo_gt {V : Type} {vis : List w64} {key txid : w64} (m : GMap w64 V)
    (hgt : ¬ key.toNat ≤ txid.toNat) :
    dropUpTo (vis ++ [key]) txid m = dropUpTo vis txid m := by
  apply GMap.map_eq; intro k
  unfold dropUpTo; rw [lookup_filter', lookup_filter']
  by_cases hk : key = k
  · subst hk; cases m !! key <;> simp [Option.filter, hgt]
  · simp only [List.mem_append, List.mem_singleton, Ne.symm hk, _root_.or_false]

theorem dropUpTo_all {V : Type} {vis : List w64} (txid : w64) (m : GMap w64 V)
    (h : ∀ k, (m !! k).isSome → k ∈ vis) :
    dropUpTo vis txid m = m.filter (fun t _ => decide (txid.toNat < t.toNat)) := by
  apply GMap.map_eq; intro k
  unfold dropUpTo; rw [lookup_filter', lookup_filter']
  cases hm : m !! k with
  | none => rfl
  | some v =>
    have := h k (by simp [hm])
    simp only [Option.filter, this, decide_true, Bool.true_and]
    by_cases hc : k.toNat ≤ txid.toNat
    · simp [hc]
    · simp [hc, show txid.toNat < k.toNat by omega]

/-- The ids of the entries of a map, gathered in the order of a list of its keys. -/
theorem flatIds_keys_filter (m : GMap w64 Pending) (keys : List w64) (txid : w64)
    (hk : ∀ k, k ∈ keys ↔ (m !! k).isSome) (hnd : keys.Nodup) :
    ((keys.filter (fun t => decide (t.toNat ≤ txid.toNat))).flatMap
      (fun t => ((m !! t).getD ⟨[], [], 0⟩).ids)).Perm
      (flatIds (m.filter (fun t _ => decide (t.toNat ≤ txid.toNat)))) := by
  have := flatIds_keys (m.filter (fun t _ => decide (t.toNat ≤ txid.toNat)))
    (keys.filter (fun t => decide (t.toNat ≤ txid.toNat)))
    (fun k => by
      rw [List.mem_filter, lookup_filter', hk k]
      cases m !! k <;> simp [Option.filter])
    (hnd.sublist List.filter_sublist)
  refine List.Perm.trans (List.Perm.of_eq (flatMap_congr_mem fun t ht => ?_)) this
  rw [List.mem_filter] at ht
  rw [lookup_filter']
  cases m !! t with
  | none => rfl
  | some v => simp only [Option.filter, ht.2, ite_true, Option.getD_some]

/-- `release(txid)` with the released ids `L` (any order): the facts `mergeSpans` needs, and the
state after it is `fl.release txid`, well-formed, with the same free and pending ids. -/
theorem release_ok {fl : FLPg} {txid : w64} {L : List w64} (hwf : fl.WF)
    (hL : L.Perm (flatIds (fl.pending.filter (fun t _ => decide (t.toNat ≤ txid.toNat))))) :
    (fl.free ++ L).Nodup ∧ (∀ y ∈ L, 2 ≤ y.toNat) ∧ fl.free.length + L.length < 2 ^ 63 ∧
    (fl.release txid).free = sortPgids (fl.free ++ L) ∧
    (fl.release txid).pending = fl.pending.filter (fun t _ => decide (txid.toNat < t.toNat)) ∧
    (fl.release txid).allocs = fl.allocs ∧
    (fl.release txid).WF ∧ (∀ x, x ∈ (fl.release txid).allIds ↔ x ∈ fl.allIds) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  have hpf : fl.pending.filter (fun t _ => decide (txid.toNat < t.toNat)) =
      fl.pending.filter (fun t v => !decide (t.toNat ≤ txid.toNat)) := by
    apply GMap.map_eq; intro k; rw [lookup_filter', lookup_filter']
    cases fl.pending !! k <;> simp [Option.filter]
  have hall : fl.allIds.Perm ((fl.free ++ L) ++
      flatIds (fl.pending.filter (fun t _ => decide (txid.toNat < t.toNat)))) := by
    unfold FLPg.allIds
    rw [pendingIds_eq, List.append_assoc, hpf]
    exact List.Perm.append_left _
      ((flatIds_filter_split fl.pending (fun t _ => decide (t.toNat ≤ txid.toNat))).trans
        (List.Perm.append_right _ hL.symm))
  have hnd : (fl.free ++ L).Nodup := (List.nodup_append.1 (hall.nodup_iff.1 h1)).1
  have hfree : (fl.release txid).free = sortPgids (fl.free ++ L) := by
    unfold FLPg.release
    simp only
    apply sortPgids_perm_eq
    exact List.Perm.append_left _ hL.symm
  have hpend : (fl.release txid).pending =
      fl.pending.filter (fun t _ => decide (txid.toNat < t.toNat)) := rfl
  have hperm : (fl.release txid).allIds.Perm fl.allIds := by
    unfold FLPg.allIds FLPg.pendingIds
    rw [hfree, hpend]
    exact (List.Perm.append_right _ (sortPgids_perm _)).trans hall.symm
  refine ⟨hnd, fun y hy => h2 y (hall.mem_iff.2 (List.mem_append_left _ (List.mem_append_right _ hy))),
    by have := hall.length_eq; simp only [List.length_append] at this; omega, hfree, hpend, rfl,
    ⟨hperm.nodup_iff.2 h1, fun id hid => h2 id (hperm.mem_iff.1 hid), ?_,
      by rw [hperm.length_eq]; exact h4, ?_⟩, fun x => hperm.mem_iff⟩
  · rw [hfree]; exact sortPgids_incr hnd
  · intro t p hp
    rw [hpend] at hp
    simp only [lookup_filter'] at hp
    apply h5 t p
    cases h : fl.pending !! t <;> simp_all [Option.filter]

end bbolt
end EtcdGrove
end Perennial
