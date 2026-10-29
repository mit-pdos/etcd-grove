/-
The compaction keys' tracked absence (`fkKey`, `Model2.lean`; the backend-compaction stage,
2026-10-29): the batch state's operations other than a put of a compaction key keep it
(`fkAbsSt_*`), and a readers' state without the keys reads none (`rtRange_fkAbs`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.WritebackLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

theorem dget_insert (S : Data) (n n' k : GoString) (b : BktData) :
    dget (S.insert n b) n' k = if n = n' then b.lookup k else dget S n' k := by
  unfold dget
  rw [GMap.lookup_insert_eq_iff]
  split <;> rfl

theorem fkAbsD_put {S : Data} {n k : GoString} (v : GoString) (h : fkAbsD S) (hk : ¬ fkKey n k) :
    fkAbsD (S.insert n ((bktOf S n).insert k v)) := by
  intro n' k' hf
  rw [dget_insert]
  split
  · rename_i hn
    subst hn
    rw [GMap.lookup_insert_eq_iff]
    split
    · rename_i hkk; subst hkk; exact absurd hf hk
    · rw [← dget_eq_bktOf]; exact h _ _ hf
  · exact h _ _ hf

theorem fkAbsD_delk {S : Data} {n k : GoString} (h : fkAbsD S) :
    fkAbsD (S.insert n ((bktOf S n).delete k)) := by
  intro n' k' hf
  rw [dget_insert]
  split
  · rename_i hn
    subst hn
    rw [GMap.lookup_delete_iff]
    split
    · rfl
    · rw [← dget_eq_bktOf]; exact h _ _ hf
  · exact h _ _ hf

theorem fkAbsD_create {S : Data} {n : GoString} (h : fkAbsD S) :
    fkAbsD (if S.lookup n = none then S.insert n ∅ else S) := by
  split
  · intro n' k' hf
    rw [dget_insert]
    split
    · rfl
    · exact h _ _ hf
  · exact h

theorem fkAbsD_delete {S : Data} {n : GoString} (h : fkAbsD S) : fkAbsD (S.delete n) := by
  intro n' k' hf
  unfold dget
  rw [GMap.lookup_delete_iff]
  split
  · rfl
  · exact h _ _ hf

theorem fkAbsB_empty (P : BParams) : fkAbsB P (∅ : GMap w64 (List Ent)) := by
  intro n k i _ _ e he
  simp [bkOf] at he

theorem fkAbsB_wbAdd {P : BParams} {B : GMap w64 (List Ent)} {n : GoString} {id : w64}
    {k v : GoString} (hP : P.Wf) (h : fkAbsB P B) (hid : P.BT.lookup n = some id)
    (hk : ¬ fkKey n k) : fkAbsB P (wbAdd B id (k, v)) := by
  intro n' k' i hf hi e he
  rw [bkOf_wbAdd] at he
  split at he
  · rename_i hii
    subst hii
    rcases List.mem_append.1 he with he | he
    · exact h n' k' id hf hi e he
    · rw [List.mem_singleton] at he
      subst he
      intro hkk
      have hn : n = n' := hP.1 n n' id hid hi
      subst hn
      simp only at hkk
      subst hkk
      exact hk hf
  · exact h n' k' i hf hi e he

theorem fkAbsB_wbMerge {P : BParams} {W R : GMap w64 (List Ent)} (hW : fkAbsB P W)
    (hR : fkAbsB P R) : fkAbsB P (wbMerge W R) := by
  intro n k i hf hi e he
  rcases mem_bkOf_wbMerge he with he | he
  · exact hR n k i hf hi e he
  · exact hW n k i hf hi e he

theorem fkAbsB_bksReset (P : BParams) (B : GMap w64 (List Ent)) : fkAbsB P (bksReset B) := by
  intro n k i _ _ e he
  rw [bkOf_bksResetC] at he
  cases he

theorem fkAbsB_writebackW (P : BParams) (W : WBuf) (R : RBuf) :
    fkAbsB P (writebackW W R).bks := by
  intro n k i _ _ e he
  rw [bkOf_writebackW] at he
  cases he

theorem fkInit_zero {D : Data} (h : fkInit D = 0) : fkAbsD D := by
  unfold fkInit at h
  split at h
  · assumption
  · cases h

theorem fkInit_of_abs {D : Data} (h : fkAbsD D) : fkInit D = 0 := by
  unfold fkInit
  simp [h]

/-! ## The batch state's operations -/

theorem fkAbsSt_put {P : BParams} {st : BSess} {bi : BucketInfo} {k v : GoString} (seq : Bool)
    (hP : P.Wf) (hbi : P.has bi) (hk : ¬ fkKey bi.name k) (h : fkAbsSt P st) :
    fkAbsSt P (st.put bi k v seq) := by
  obtain ⟨hrv, hS, hW⟩ := h
  refine ⟨hrv, fkAbsD_put v hS hk, ?_⟩
  unfold BSess.put
  cases seq
  · exact fkAbsB_wbAdd hP hW hbi hk
  · exact fkAbsB_wbAdd hP hW hbi hk

theorem fkAbsSt_del {P : BParams} {st : BSess} {bi : BucketInfo} {k : GoString}
    (h : fkAbsSt P st) : fkAbsSt P (st.del bi k) :=
  ⟨h.1, fkAbsD_delk h.2.1, h.2.2⟩

theorem fkAbsSt_create {P : BParams} {st : BSess} {bi : BucketInfo} (h : fkAbsSt P st) :
    fkAbsSt P (st.create bi) :=
  ⟨h.1, fkAbsD_create h.2.1, h.2.2⟩

theorem fkAbsSt_delBucket {P : BParams} {st : BSess} {bi : BucketInfo} (h : fkAbsSt P st) :
    fkAbsSt P (st.delBucket bi) :=
  ⟨h.1, fkAbsD_delete h.2.1, h.2.2⟩

theorem fkAbsSt_wb {P : BParams} {st : BSess} (h : fkAbsSt P st) : fkAbsSt P (wbSt P st) :=
  ⟨⟨h.1.1, fkAbsB_wbMerge h.2.2 h.1.2⟩, h.2.1, fkAbsB_writebackW P st.W st.R⟩

theorem fkAbsSt_commit {P : BParams} {st : BSess} {C' : Data} {tx' : Loc} {cnt' : BCnt}
    (h : fkAbsSt P st) (hC : C' = st.S ∨ C' = st.C) : fkAbsSt P (commitSt st C' tx' cnt') := by
  refine ⟨⟨?_, fkAbsB_bksReset P _⟩, h.2.1, h.2.2⟩
  rcases hC with rfl | rfl
  · exact h.2.1
  · exact h.1.1

theorem fkAbsSt_setHw {P : BParams} {st : BSess} (x : Bool) (h : fkAbsSt P st) :
    fkAbsSt P (st.setHw x) := h

/-! ## Reads -/

/-- A readers' state with no compaction key reads none at one: `UnsafeRange(Meta, k, nil, _)`
of a compaction key `k` returns nothing. -/
theorem rtRange_fkAbs {P : BParams} {rv : RView} {bi : BucketInfo} {kb : GoString} (lim : w64)
    (h : fkAbsRv P rv) (hbi : P.has bi) (hk : fkKey bi.name kb) :
    rtRange rv bi kb [] lim = [] := by
  have hbuf : bbRange (bkOf rv.2.bks bi.id) kb [] (rangeLimit [] lim) = [] := by
    unfold bbRange
    split
    · rfl
    · rename_i e rest hd
      simp only [↓reduceIte]
      have he : e ∈ bkOf rv.2.bks bi.id := by
        have : e ∈ (bkOf rv.2.bks bi.id).dropWhile (fun e => decide (strLt e.1 kb)) := by
          rw [hd]; exact List.mem_cons_self
        exact (List.dropWhile_sublist _).subset this
      have hne := h.2 bi.name kb bi.id hk hbi e he
      simp [hne]
  unfold rtRange
  simp only [hbuf, List.length_nil, List.append_nil]
  have hlim : rangeLimit [] lim = W64 1 := by simp [rangeLimit]
  rw [hlim]
  have h0 : ¬ (((0 : Nat) : Int) = sint.Z (W64 1)) := by decide
  simp only [h0, ↓reduceIte]
  unfold cursorRange
  simp only [↓reduceIte]
  -- no entry of the committed bucket has the key
  have hnone : ∀ e ∈ bktEnts (bktOf rv.1 bi.name), e.1 ≠ kb := by
    intro e he hek
    have hm : e ∈ (bktOf rv.1 bi.name).toList := List.mem_mergeSort.1 he
    have hl : (bktOf rv.1 bi.name).lookup e.1 = some e.2 := (GMap.mem_toList _ _ _).1 hm
    rw [hek, ← dget_eq_bktOf, h.1 bi.name kb hk] at hl
    cases hl
  generalize hr : (bktEnts (bktOf rv.1 bi.name)).drop _ = rest
  have hsub : ∀ e ∈ rest, e.1 ≠ kb := by
    intro e he
    rw [← hr] at he
    exact hnone e (List.mem_of_mem_drop he)
  cases rest with
  | nil => rfl
  | cons e rest =>
    simp [List.takeWhile, hsub e List.mem_cons_self]

end backend
end EtcdGrove
end Perennial
