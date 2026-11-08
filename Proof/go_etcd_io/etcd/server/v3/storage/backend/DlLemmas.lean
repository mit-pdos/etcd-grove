/-
**The safe-range buckets' deleted entries** (the user's decision, 2026-11-04, probe M2: a snapshot's
observation knows the safe-range bucket exactly): the pure lemmas of `dlR`, `dlsOk` and `dlVd`
(`Model2.lean`), how each operation of the batch transaction keeps the agreement of the deleted
entries, the logical view and the writer's contents. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.FkLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-- The writer's contents' view at a key: the data's, off the hook's buckets. -/
theorem sData_lookupD (P : BParams) (S : Data) (nk : GoString × GoString) :
    (sData P S).lookup nk = if P.HB nk.1 then none else dget S nk.1 nk.2 := by
  unfold sData
  show (if P.HB nk.1 then none else vOf P (S, ⟨∅, W64 0⟩) nk.1 nk.2) = _
  rw [vOf_emptyR]

theorem dget_bktOf (D : Data) (n k : GoString) : dget D n k = (bktOf D n).lookup k := by
  unfold dget bktOf
  cases D.lookup n <;> rfl

theorem dlR_lookup (P : BParams) (X : GMap (GoString × GoString) GoString) (nk : GoString × GoString) :
    (dlR P X).lookup nk = if P.SB nk.1 = true ∧ P.HB nk.1 = false then X.lookup nk else none := by
  unfold dlR
  show (X.lookup nk).filter _ = _
  cases hX : X.lookup nk <;> by_cases h1 : P.SB nk.1 = true <;> by_cases h2 : P.HB nk.1 = false <;>
    simp_all [Option.filter]

/-- On a safe-range key off the hook's buckets, the deleted entries are their safe-range part's. -/
theorem dlR_lookup_sb (P : BParams) (X : GMap (GoString × GoString) GoString)
    {nk : GoString × GoString} (h1 : P.SB nk.1 = true) (h2 : P.HB nk.1 = false) :
    (dlR P X).lookup nk = X.lookup nk := by
  rw [dlR_lookup]; simp [h1, h2]

/-- **The agreement depends on the writer's contents and the safe-range deleted entries only.** -/
theorem dlsOk_congr {P : BParams} {st st' : BSess} {L : GMap (GoString × GoString) GoString}
    (hS : sData P st'.S = sData P st.S) (hD : dlR P st'.dl = dlR P st.dl) (h : dlsOk P st L) :
    dlsOk P st' L := by
  have hd : ∀ nk, P.SB nk.1 = true → P.HB nk.1 = false → st'.dl.lookup nk = st.dl.lookup nk := by
    intro nk h1 h2
    rw [← dlR_lookup_sb P st'.dl h1 h2, ← dlR_lookup_sb P st.dl h1 h2, hD]
  refine ⟨fun nk h1 h2 hL hs => ?_, fun nk h1 h2 hx => ?_⟩
  · rw [hd nk h1 h2]; exact h.1 nk h1 h2 hL (by rw [← hS]; exact hs)
  · rw [hd nk h1 h2] at hx
    have := h.2 nk h1 h2 hx
    exact ⟨by rw [hS]; exact this.1, this.2⟩

/-! ### The operations -/

theorem sData_put_lookup (P : BParams) (st : BSess) (bi : BucketInfo) (k v : GoString) (seq : Bool)
    (nk : GoString × GoString) :
    (sData P (st.put bi k v seq).S).lookup nk =
      if P.HB nk.1 then none else if nk = (bi.name, k) then some v else (sData P st.S).lookup nk := by
  rw [sData_lookupD, sData_lookupD]
  by_cases hb : P.HB nk.1
  · simp [hb]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [dget_bktOf, dget_bktOf]
    show (bktOf (st.S.insert bi.name ((bktOf st.S bi.name).insert k v)) nk.1).lookup nk.2 = _
    by_cases hn : nk.1 = bi.name
    · have hb' : bktOf (st.S.insert bi.name ((bktOf st.S bi.name).insert k v)) nk.1 =
          (bktOf st.S bi.name).insert k v := by
        unfold bktOf; rw [hn, GMap.lookup_insert]; rfl
      rw [hb']
      by_cases hk : nk.2 = k
      · have : nk = (bi.name, k) := Prod.ext hn hk
        simp only [this, ↓reduceIte]
        exact GMap.lookup_insert _ _ _
      · have : nk ≠ (bi.name, k) := fun h => hk (by rw [h])
        simp only [this, ↓reduceIte]
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), hn]
    · have hb' : bktOf (st.S.insert bi.name ((bktOf st.S bi.name).insert k v)) nk.1 =
          bktOf st.S nk.1 := by
        unfold bktOf; rw [GMap.lookup_insert_ne _ _ (Ne.symm hn)]
      have : nk ≠ (bi.name, k) := fun h => hn (by rw [h])
      rw [hb']; simp only [this, ↓reduceIte]

theorem sData_del_lookup (P : BParams) (st : BSess) (bi : BucketInfo) (k : GoString)
    (nk : GoString × GoString) :
    (sData P (st.del bi k).S).lookup nk =
      if nk = (bi.name, k) then none else (sData P st.S).lookup nk := by
  rw [sData_lookupD, sData_lookupD]
  by_cases hb : P.HB nk.1
  · simp [hb]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [dget_bktOf, dget_bktOf]
    show (bktOf (st.S.insert bi.name ((bktOf st.S bi.name).delete k)) nk.1).lookup nk.2 = _
    by_cases hn : nk.1 = bi.name
    · have hb' : bktOf (st.S.insert bi.name ((bktOf st.S bi.name).delete k)) nk.1 =
          (bktOf st.S bi.name).delete k := by
        unfold bktOf; rw [hn, GMap.lookup_insert]; rfl
      rw [hb']
      by_cases hk : nk.2 = k
      · have : nk = (bi.name, k) := Prod.ext hn hk
        simp only [this, ↓reduceIte]
        exact GMap.lookup_delete _ _
      · have : nk ≠ (bi.name, k) := fun h => hk (by rw [h])
        simp only [this, ↓reduceIte]
        rw [GMap.lookup_delete_ne _ (Ne.symm hk), hn]
    · have hb' : bktOf (st.S.insert bi.name ((bktOf st.S bi.name).delete k)) nk.1 =
          bktOf st.S nk.1 := by
        unfold bktOf; rw [GMap.lookup_insert_ne _ _ (Ne.symm hn)]
      have : nk ≠ (bi.name, k) := fun h => hn (by rw [h])
      rw [hb']; simp only [this, ↓reduceIte]

theorem del_dl_lookup (st : BSess) (bi : BucketInfo) (k : GoString) (nk : GoString × GoString) :
    (st.del bi k).dl.lookup nk =
      if nk = (bi.name, k) then ((bktOf st.S bi.name).lookup k).or (st.dl.lookup nk)
      else st.dl.lookup nk := by
  unfold BSess.del
  simp only
  cases hv : (bktOf st.S bi.name).lookup k with
  | some v =>
    by_cases h : nk = (bi.name, k)
    · subst h; simp only [↓reduceIte, Option.some_or]; exact GMap.lookup_insert _ _ _
    · simp only [h, ↓reduceIte]; exact GMap.lookup_insert_ne _ _ (Ne.symm h)
  | none =>
    simp only [Option.none_or]
    split <;> rfl

/-- **A put keeps the agreement**, its key not a deleted safe-range entry. -/
theorem dlsOk_put {P : BParams} {st : BSess} {L : GMap (GoString × GoString) GoString}
    {bi : BucketInfo} {k v : GoString} (seq : Bool)
    (hk : P.SB bi.name = true → P.HB bi.name = false → st.dl.lookup (bi.name, k) = none)
    (h : dlsOk P st L) : dlsOk P (st.put bi k v seq) L := by
  have hdl : (st.put bi k v seq).dl = st.dl := rfl
  refine ⟨fun nk h1 h2 hL hs => ?_, fun nk h1 h2 hx => ?_⟩
  · rw [hdl]
    rw [sData_put_lookup] at hs
    simp only [h2, Bool.false_eq_true, ↓reduceIte] at hs
    split at hs
    · cases hs
    · exact h.1 nk h1 h2 hL hs
  · rw [hdl] at hx
    have := h.2 nk h1 h2 hx
    refine ⟨?_, this.2⟩
    rw [sData_put_lookup]
    simp only [h2, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i he; subst he; exact absurd (hk h1 h2) hx
    · exact this.1

/-- **A delete keeps the agreement**, a present safe-range entry it deletes being the logical
view's. -/
theorem dlsOk_del {P : BParams} {st : BSess} {L : GMap (GoString × GoString) GoString}
    {bi : BucketInfo} {k : GoString}
    (hL : P.SB bi.name = true → P.HB bi.name = false →
      (sData P st.S).lookup (bi.name, k) ≠ none → L.lookup (bi.name, k) ≠ none)
    (h : dlsOk P st L) : dlsOk P (st.del bi k) L := by
  refine ⟨fun nk h1 h2 hLn hs => ?_, fun nk h1 h2 hx => ?_⟩
  · rw [del_dl_lookup]
    rw [sData_del_lookup] at hs
    split
    · rename_i he
      subst he
      cases hb : (bktOf st.S bi.name).lookup k with
      | some w => simp
      | none =>
        simp only [Option.none_or]
        apply h.1 _ h1 h2 hLn
        rw [sData_lookupD]; simp only [h2, Bool.false_eq_true, ↓reduceIte]
        rw [dget_bktOf]; exact hb
    · rename_i he
      simp only [he, ↓reduceIte] at hs
      exact h.1 nk h1 h2 hLn hs
  · rw [del_dl_lookup] at hx
    constructor
    · rw [sData_del_lookup]
      split
      · rfl
      · rename_i he; simp only [he, ↓reduceIte] at hx; exact (h.2 nk h1 h2 hx).1
    · split at hx
      · rename_i he
        subst he
        cases hb : (bktOf st.S bi.name).lookup k with
        | some w =>
          apply hL h1 h2
          rw [sData_lookupD]; simp only [h2, Bool.false_eq_true, ↓reduceIte]
          rw [dget_bktOf, hb]; simp
        | none =>
          rw [hb, Option.none_or] at hx
          exact (h.2 _ h1 h2 hx).2
      · exact (h.2 nk h1 h2 hx).2

/-- A delete off the safe-range buckets (or in a hook's bucket) leaves the safe-range deleted
entries. -/
theorem dlR_del_other (P : BParams) (st : BSess) (bi : BucketInfo) (k : GoString)
    (h : P.SB bi.name = false ∨ P.HB bi.name = true) : dlR P (st.del bi k).dl = dlR P st.dl := by
  apply GMap.ext
  intro nk
  rw [dlR_lookup, dlR_lookup, del_dl_lookup]
  split
  · rename_i hc
    split
    · rename_i he
      subst he
      rcases h with h | h
      · rw [h] at hc; simp at hc
      · rw [h] at hc; simp at hc
    · rfl
  · rfl

theorem sData_create (P : BParams) (st : BSess) (bi : BucketInfo) :
    sData P (st.create bi).S = sData P st.S := by
  apply GMap.ext
  intro nk
  rw [sData_lookupD, sData_lookupD]
  split
  · rfl
  · show dget (if st.S.lookup bi.name = none then st.S.insert bi.name ∅ else st.S) nk.1 nk.2 = _
    split
    · rename_i hn
      unfold dget
      by_cases he : nk.1 = bi.name
      · rw [he, GMap.lookup_insert, hn]; rfl
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)]
    · rfl

/-- A bucket's creation keeps the agreement. -/
theorem dlsOk_create {P : BParams} {st : BSess} {L : GMap (GoString × GoString) GoString}
    {bi : BucketInfo} (h : dlsOk P st L) : dlsOk P (st.create bi) L :=
  dlsOk_congr (sData_create P st bi) rfl h

theorem sData_delBucket_lookup (P : BParams) (st : BSess) (bi : BucketInfo)
    (nk : GoString × GoString) (hn : nk.1 ≠ bi.name) :
    (sData P (st.delBucket bi).S).lookup nk = (sData P st.S).lookup nk := by
  rw [sData_lookupD, sData_lookupD]
  split
  · rfl
  · show dget (st.S.delete bi.name) nk.1 nk.2 = _
    unfold dget
    rw [GMap.lookup_delete_ne _ (Ne.symm hn)]

/-- A non-safe-range bucket's deletion keeps the agreement. -/
theorem dlsOk_delBucket {P : BParams} {st : BSess} {L : GMap (GoString × GoString) GoString}
    {bi : BucketInfo} (hSB : P.SB bi.name = false) (h : dlsOk P st L) :
    dlsOk P (st.delBucket bi) L := by
  have hdl : (st.delBucket bi).dl = st.dl := rfl
  refine ⟨fun nk h1 h2 hL hs => ?_, fun nk h1 h2 hx => ?_⟩
  · have hn : nk.1 ≠ bi.name := fun he => by rw [he, hSB] at h1; cases h1
    rw [hdl]; rw [sData_delBucket_lookup P st bi nk hn] at hs; exact h.1 nk h1 h2 hL hs
  · have hn : nk.1 ≠ bi.name := fun he => by rw [he, hSB] at h1; cases h1
    rw [hdl] at hx
    rw [sData_delBucket_lookup P st bi nk hn]; exact h.2 nk h1 h2 hx

/-- **What the agreement says of the writer's contents' view**: the deleted entries `dlR` are
exactly the logical view's safe-range entries missing from it (`dlVd`). -/
theorem dlVd_of_dlsOk {P : BParams} {st : BSess} {L : GMap (GoString × GoString) GoString}
    (h : dlsOk P st L) : dlVd P (sData P st.S) L (dlR P st.dl) := by
  refine ⟨fun nk h1 h2 hL hs => ?_, fun nk hx => ?_⟩
  · rw [dlR_lookup_sb P _ h1 h2]; exact h.1 nk h1 h2 hL hs
  · rw [dlR_lookup] at hx
    split at hx
    · rename_i hc
      have := h.2 nk hc.1 hc.2 hx
      exact ⟨hc.1, hc.2, this.1, this.2⟩
    · exact absurd rfl hx

/-- The agreement at an empty deleted set and the logical view the writer's contents' view (a new
backend). -/
theorem dlsOk_exact {P : BParams} {st : BSess} (hdl : st.dl = ∅) : dlsOk P st (sData P st.S) := by
  refine ⟨fun nk _ _ hL hs => absurd hs hL, fun nk _ _ hx => ?_⟩
  rw [hdl] at hx; exact absurd rfl hx

/-! ### The part that holds in a window, and the window's form -/

theorem dlsS_of_dlsOk {P : BParams} {st : BSess} {L : GMap (GoString × GoString) GoString}
    (h : dlsOk P st L) : dlsS P st := fun nk h1 h2 hx => (h.2 nk h1 h2 hx).1

theorem dlsS_congr {P : BParams} {st st' : BSess} (hS : sData P st'.S = sData P st.S)
    (hD : dlR P st'.dl = dlR P st.dl) (h : dlsS P st) : dlsS P st' := by
  intro nk h1 h2 hx
  rw [← dlR_lookup_sb P st'.dl h1 h2, hD, dlR_lookup_sb P st.dl h1 h2] at hx
  rw [hS]; exact h nk h1 h2 hx

theorem dlsS_put {P : BParams} {st : BSess} {bi : BucketInfo} {k v : GoString} (seq : Bool)
    (hk : P.SB bi.name = true → P.HB bi.name = false → st.dl.lookup (bi.name, k) = none)
    (h : dlsS P st) : dlsS P (st.put bi k v seq) := by
  intro nk h1 h2 hx
  have hdl : (st.put bi k v seq).dl = st.dl := rfl
  rw [hdl] at hx
  rw [sData_put_lookup]
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i he; subst he; exact absurd (hk h1 h2) hx
  · exact h nk h1 h2 hx

theorem dlsS_del {P : BParams} {st : BSess} {bi : BucketInfo} {k : GoString} (h : dlsS P st) :
    dlsS P (st.del bi k) := by
  intro nk h1 h2 hx
  rw [sData_del_lookup]
  split
  · rfl
  · rename_i he
    rw [del_dl_lookup] at hx
    simp only [he, ↓reduceIte] at hx
    exact h nk h1 h2 hx

theorem dlsS_create {P : BParams} {st : BSess} {bi : BucketInfo} (h : dlsS P st) :
    dlsS P (st.create bi) := dlsS_congr (sData_create P st bi) rfl h

theorem dlsS_delBucket {P : BParams} {st : BSess} {bi : BucketInfo} (hSB : P.SB bi.name = false)
    (h : dlsS P st) : dlsS P (st.delBucket bi) := by
  intro nk h1 h2 hx
  have hn : nk.1 ≠ bi.name := fun he => by rw [he, hSB] at h1; cases h1
  rw [sData_delBucket_lookup P st bi nk hn]; exact h nk h1 h2 hx

/-- **An operation keeps the batch lock's agreement**: the part that holds always, the full one,
the window marker and the hook's window kept. -/
theorem dlsW_step {P : BParams} {st st' : BSess} {L : GMap (GoString × GoString) GoString}
    (hS : dlsS P st → dlsS P st') (hO : dlsOk P st L → dlsOk P st' L) (hwin : st'.win = st.win)
    (hhw : st'.cnt.hw = st.cnt.hw) (h : dlsW P st L) : dlsW P st' L :=
  ⟨hS h.1, fun hw => hO (h.2.1 (hwin ▸ hw)), fun hh => hwin ▸ h.2.2 (hhw ▸ hh)⟩

/-- The agreement at a state reading as its logical view `L` with nothing deleted (a new backend). -/
theorem dlsW_exact {P : BParams} {st : BSess} (hdl : st.dl = ∅) (hwin : st.win = false) :
    dlsW P st (sData P st.S) :=
  ⟨fun nk _ _ hx => by rw [hdl] at hx; exact absurd rfl hx, fun _ => dlsOk_exact hdl,
    fun _ => hwin⟩

end backend
end EtcdGrove
end Perennial
