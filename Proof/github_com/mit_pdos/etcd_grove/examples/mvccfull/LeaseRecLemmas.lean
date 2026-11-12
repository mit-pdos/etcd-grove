/-
The lease bucket's records after a grant and a revoke (pure; `leaseRecsOk`, `runner.apply`'s grant
and revoke arms). Lean-first (no Rocq counterpart).

A record's key is its id's 8 big-endian bytes (`leaseRecEnc`), so the bucket's entries in key order
are the records in increasing id order: a grant of an id above every live one appends its record
(`leaseRecsOk_grant`); a revoke removes its record (`leaseRecsOk_revoke`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LogModel
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ModelLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc

section model
variable [GooseExts]

/-- **Two key-sorted entry lists with the same entries are equal.** -/
theorem ents_eq_of_sorted_mem : ∀ {l1 l2 : List backend.Ent}, backend.entsSorted l1 →
    backend.entsSorted l2 → (∀ e, e ∈ l1 ↔ e ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: _, [], _, _, h => absurd ((h a).1 (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: l1, b :: l2, h1, h2, h => by
    unfold backend.entsSorted at h1 h2
    have ha := (List.pairwise_cons.1 h1).1
    have hb := (List.pairwise_cons.1 h2).1
    have hab : a = b := by
      refine Classical.byContradiction (fun hne => ?_)
      have h1' : a ∈ l2 := by
        rcases List.mem_cons.1 ((h a).1 (List.mem_cons_self ..)) with e | e
        · exact absurd e hne
        · exact e
      have h2' : b ∈ l1 := by
        rcases List.mem_cons.1 ((h b).2 (List.mem_cons_self ..)) with e | e
        · exact absurd e.symm hne
        · exact e
      exact go.goStringLt_asymm (hb a h1') (ha b h2')
    subst hab
    congr 1
    refine ents_eq_of_sorted_mem (List.pairwise_cons.1 h1).2 (List.pairwise_cons.1 h2).2 ?_
    intro e
    constructor
    · intro he
      rcases List.mem_cons.1 ((h e).1 (List.mem_cons_of_mem _ he)) with e' | e'
      · subst e'; exact absurd (ha _ he) (go.goStringLt_irrefl _)
      · exact e'
    · intro he
      rcases List.mem_cons.1 ((h e).2 (List.mem_cons_of_mem _ he)) with e' | e'
      · subst e'; exact absurd (hb _ he) (go.goStringLt_irrefl _)
      · exact e'

theorem bktEnts_sorted' (m : backend.BktData) : backend.entsSorted (backend.bktEnts m) := by
  unfold backend.bktEnts
  have hn : ((m.toList.mergeSort backend.entLe).map Prod.fst).Nodup :=
    (((List.mergeSort_perm m.toList backend.entLe).map Prod.fst).nodup_iff).2
      (GMap.toList_keys_nodup m)
  have hle := backend.mergeSort_pairwise m.toList
  rw [List.Nodup, List.pairwise_map] at hn
  unfold backend.entsSorted
  refine (hle.and hn).imp (fun ⟨h1, h2⟩ => ?_)
  rcases backend.strLt_total h1 with e | e
  · exact absurd e.symm h2
  · exact e

theorem mem_bktEnts' (m : backend.BktData) (e : backend.Ent) :
    e ∈ backend.bktEnts m ↔ m.lookup e.1 = some e.2 := by
  unfold backend.bktEnts
  rw [(List.mergeSort_perm m.toList backend.entLe).mem_iff]
  exact GMap.mem_toList m e.1 e.2

theorem leaseRecEnc_key_lt (a b : w64 × w64 × w64) (h : uint.Z a.1 < uint.Z b.1) :
    go.GoStringLt (lease.leaseRecEnc a).1 (lease.leaseRecEnc b).1 := by
  have := mvcc.u64Be_lt h
  simpa [lease.leaseRecEnc, u64Be] using this

/-- **A grant of an id above every live one appends its record.** -/
theorem leaseRecsOk_grant (r : GMap GoString backend.BktData) (L : List w64) (id t : w64)
    (h : leaseRecsOk r L) (hL : ∀ l ∈ L, 0 ≤ sint.Z l ∧ sint.Z l < sint.Z id) (hid : 0 < sint.Z id)
    (ht : 3600 ≤ sint.Z t) :
    leaseRecsOk (mvcc.rbSet r mvcc.leaseName (u64Le id).reverse (lease.leaseEnc id t (W64 0)))
      (L ++ [id]) := by
  obtain ⟨recs, h1, h2, h3⟩ := h
  refine ⟨recs ++ [(id, t, W64 0)], ?_, by rw [List.map_append, h2]; rfl, ?_⟩
  · unfold mvcc.rbSet
    rw [GMap.lookup_insert]
    simp only [Option.getD_some]
    generalize hMd : (r !! mvcc.leaseName).getD ∅ = M at h1 ⊢
    apply ents_eq_of_sorted_mem (bktEnts_sorted' _)
    · rw [List.map_append]
      unfold backend.entsSorted
      rw [List.pairwise_append]
      refine ⟨?_, by simp, ?_⟩
      · have := bktEnts_sorted' M
        rw [h1] at this; exact this
      · intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        apply leaseRecEnc_key_lt
        have hxL : x.1 ∈ L := by rw [← h2]; exact List.mem_map_of_mem hx
        have := hL _ hxL
        simp only
        have e1 : uint.Z x.1 = sint.Z x.1 := by word
        have e2 : uint.Z id = sint.Z id := by word
        omega
    · intro e
      rw [mem_bktEnts', List.map_append, List.mem_append]
      have hM : ∀ e, e ∈ recs.map lease.leaseRecEnc ↔ M.lookup e.1 = some e.2 := by
        intro e; rw [← h1, mem_bktEnts']
      by_cases hk : e.1 = (u64Le id).reverse
      · rw [hk, GMap.lookup_insert]
        have hkx : ∀ x ∈ recs, (lease.leaseRecEnc x).1 ≠ (u64Le id).reverse := by
          intro x hx heq
          have hxL : x.1 ∈ L := by rw [← h2]; exact List.mem_map_of_mem hx
          have := hL _ hxL
          have e1 : uint.Z x.1 = sint.Z x.1 := by word
          have e2 : uint.Z id = sint.Z id := by word
          have hlt := leaseRecEnc_key_lt x (id, t, W64 0) (by simp only; omega)
          rw [heq] at hlt
          exact go.goStringLt_irrefl _ (by simpa [lease.leaseRecEnc] using hlt)
        constructor
        · intro he
          right
          obtain ⟨e1, e2⟩ := e
          simp only at hk he
          subst hk
          injection he with he
          subst he
          simp [lease.leaseRecEnc]
        · rintro (h | h)
          · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
            exact absurd hk (hkx x hx)
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
            subst h
            simp [lease.leaseRecEnc]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), ← hM]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | h)
          · exact h
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
            subst h
            exact absurd (by simp [lease.leaseRecEnc]) hk
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h3 x hx
    · simp at hx; subst hx; exact ht

theorem leaseRecEnc_key_ne (a b : w64 × w64 × w64) (h : a.1 ≠ b.1) :
    (lease.leaseRecEnc a).1 ≠ (lease.leaseRecEnc b).1 := by
  have : uint.Z a.1 ≠ uint.Z b.1 := by
    intro e; apply h; apply BitVec.eq_of_toNat_eq
    have e1 : uint.Z a.1 = (a.1.toNat : Int) := rfl
    have e2 : uint.Z b.1 = (b.1.toNat : Int) := rfl
    omega
  rcases Int.lt_or_gt_of_ne this with hl | hl
  · intro e; have := leaseRecEnc_key_lt a b hl; rw [e] at this; exact go.goStringLt_irrefl _ this
  · intro e; have := leaseRecEnc_key_lt b a hl; rw [e] at this; exact go.goStringLt_irrefl _ this

/-- **A revoke removes its record.** -/
theorem leaseRecsOk_revoke (r : GMap GoString backend.BktData) (L : List w64) (id : w64)
    (h : leaseRecsOk r L) :
    leaseRecsOk (mvcc.rbDel r mvcc.leaseName (u64Le id).reverse) (L.filter (· != id)) := by
  obtain ⟨recs, h1, h2, h3⟩ := h
  refine ⟨recs.filter (fun x => x.1 != id), ?_, ?_, ?_⟩
  · unfold mvcc.rbDel
    rw [GMap.lookup_insert]
    simp only [Option.getD_some]
    generalize hMd : (r !! mvcc.leaseName).getD ∅ = M at h1 ⊢
    apply ents_eq_of_sorted_mem (bktEnts_sorted' _)
    · have hs := bktEnts_sorted' M
      rw [h1] at hs
      unfold backend.entsSorted at hs ⊢
      exact hs.sublist ((List.filter_sublist).map _)
    · intro e
      rw [mem_bktEnts', GMap.lookup_delete_Some]
      constructor
      · rintro ⟨hne, hl⟩
        have he : e ∈ recs.map lease.leaseRecEnc := by rw [← h1, mem_bktEnts']; exact hl
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
        refine List.mem_map_of_mem (List.mem_filter.2 ⟨hx, ?_⟩)
        have : x.1 ≠ id := by
          intro e; apply hne; simp [lease.leaseRecEnc, e]
        simpa using this
      · intro he
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
        obtain ⟨hx, hxi⟩ := List.mem_filter.1 hx
        have hxi' : x.1 ≠ id := by simpa using hxi
        refine ⟨?_, ?_⟩
        · have := leaseRecEnc_key_ne (id, W64 0, W64 0) x (Ne.symm hxi')
          simpa [lease.leaseRecEnc] using this
        · have : lease.leaseRecEnc x ∈ recs.map lease.leaseRecEnc := List.mem_map_of_mem hx
          rw [← h1, mem_bktEnts'] at this; exact this
  · rw [← h2]
    clear h1 h2 h3
    induction recs with
    | nil => rfl
    | cons x xs ih =>
      by_cases hx : x.1 = id
      · simp [List.filter, hx, ih]
      · have hb : (x.1 != id) = true := by simpa using hx
        simp only [List.filter, hb, List.map_cons, List.map, ih]
  · intro x hx; exact h3 x (List.mem_filter.1 hx).1

end model

end mvccfull
end EtcdGrove
end Perennial
