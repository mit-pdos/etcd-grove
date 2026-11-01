/-
The proof of `Spec/os/File__WriteAt.lean`: one attempt (`PWriteStart`, `PWriteFinish`) per
iteration of the model's loop, which retries only on `EINTR`, by Löb induction; the invariant is
the file as a write of the first `j` bytes left it (`pwBytes_retry`).
-/
module

public import Spec.os.File__WriteAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.WriteAt.wp_proof : os.File.WriteAt.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d q m xs hwr hoff hn hn2 hxl hq
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hm, Hbs, Hc⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl dqs data $$ Hsl with %Hlen
  icases ownSlice_wf sl dqs data $$ Hsl with %Hwf
  wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_auto
  have hl0 : sl.len ≠ W64 0 := by
    intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; omega
  rw [decide_eq_false hl0]
  wp_pure
  wp_pure
  -- the invariant: the file as a write of the first `j` bytes left it
  have hm0 : m = { m with size := pwSize m.size off.toNat 0, hi := m.hi } := by
    simp [pwSize]
  generalize hj0 : (0 : Nat) = j
  have hj : j ≤ data.length := by omega
  have hys : xs.map Prod.fst = (pwBytes m.size off.toNat data j xs).map Prod.fst := by
    rw [← hj0, pwBytes_zero _ _ _ _ hxl]
  have hh : m.hi ≤ m.hi := Nat.le_refl _
  ihave Hm := (show osMeta (GF := GF) d.path (DFrac.own q) (some m) ⊢
    osMeta d.path (DFrac.own q) (some { m with size := pwSize m.size off.toNat j, hi := m.hi }) by
      rw [← hj0, ← hm0]) $$ Hm
  clear hm0
  obtain ⟨ys, hy⟩ : ∃ ys, ys = xs := ⟨_, rfl⟩
  ihave Hbs := (show osBytes (GF := GF) d.path (min off.toNat m.size) (DFrac.own 1) xs ⊢
    osBytes d.path (min off.toNat m.size) (DFrac.own 1) ys by rw [hy]) $$ Hbs
  replace hys : ys.map Prod.fst = (pwBytes m.size off.toNat data j xs).map Prod.fst := by
    rw [hy]; exact hys
  clear hy
  obtain ⟨h, hhe⟩ : ∃ h, h = m.hi := ⟨_, rfl⟩
  ihave Hm := (show osMeta (GF := GF) d.path (DFrac.own q)
      (some { m with size := pwSize m.size off.toNat j, hi := m.hi }) ⊢
    osMeta d.path (DFrac.own q) (some { m with size := pwSize m.size off.toNat j, hi := h })
      by rw [hhe]) $$ Hm
  replace hh : m.hi ≤ h := by omega
  clear hhe
  clear hj0
  iloeb as IH generalizing %j %ys %h %hj %hys %hh Hm Hbs Hc Hosfd Hsl Hfd HΦ
  -- one attempt
  wp_auto
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  have hz : sl.len - W64 0 = sl.len := BitVec.sub_zero sl.len
  have hmax : ¬ (sint.Z (W64 1073741824) < sint.Z (sl.len - W64 0)) := by
    rw [hz, hslz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
  rw [decide_eq_false hmax]
  wp_auto
  have hsb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega
  rw [if_pos hsb, ← slice_slice_trivial, show off + W64 0 = off from BitVec.add_zero off]
  wp_apply wp_bytes_to_string sl data dqs $$ Hsl as Hsl
  -- the bytes and cells this attempt takes
  have hyl : ys.length = min (off.toNat + data.length) (pwSize m.size off.toNat j) -
      min off.toNat m.size := by
    have := congrArg List.length hys; simp only [List.length_map, pwBytes_length] at this; exact this
  have hsz : m.size ≤ pwSize m.size off.toNat j := by unfold pwSize; split <;> omega
  have hPl : (ys.take (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).length =
      min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size := by
    rw [List.length_take]; omega
  ihave ⟨Hbs1, Hbs2⟩ := (show osBytes (GF := GF) d.path (min off.toNat m.size) (DFrac.own 1) ys ⊢
      osBytes d.path (min off.toNat m.size) (DFrac.own 1)
        (ys.take (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)) ∗
      osBytes d.path (min off.toNat (pwSize m.size off.toNat j)) (DFrac.own 1)
        (ys.drop (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)) by
    conv => lhs; rw [← List.take_append_drop
      (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size) ys]
    unfold osBytes
    refine (bytesG_append _ _ _ _ _ _).1.trans ?_
    rw [hPl, show min off.toNat m.size + (min off.toNat (pwSize m.size off.toNat j) -
      min off.toNat m.size) = min off.toNat (pwSize m.size off.toNat j) by omega]) $$ Hbs
  ihave ⟨Hc1, Hc2⟩ := mcellsAny_split m.maps (min off.toNat m.size)
    (min off.toNat (pwSize m.size off.toNat j)) (off.toNat + data.length) (by omega) (by omega) $$ Hc
  wp_apply wp_PWriteStart fd off data dq d q { m with size := pwSize m.size off.toNat j, hi := h }
    (ys.drop (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size))
    CoPset.subseteq_top hwr hoff (by
      simp only [List.length_drop]
      show ys.length - _ = min (off.toNat + data.length) (pwSize m.size off.toNat j) -
        min off.toNat (pwSize m.size off.toNat j)
      omega)
    (fun hr => hq (by simp only at hr; omega)) $$ Hinv Hosfd Hm Hbs2 Hc2 as %t Hosfd Ht
  wp_apply wp_PWriteFinish t d.path off.toNat data q
    { m with size := pwSize m.size off.toNat j, hi := h }
    (ys.drop (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size))
    CoPset.subseteq_top $$ Hinv Ht as %k %e %hke Hm Hbs2 Hc2
  obtain ⟨hk, hke⟩ := hke
  -- the file as a write of the first `max j k` bytes left it
  ihave Hm := (show osMeta (GF := GF) d.path (DFrac.own q)
      (some { pwMeta { m with size := pwSize m.size off.toNat j, hi := h } off.toNat data.length with
        size := pwSize (pwSize m.size off.toNat j) off.toNat k }) ⊢
    osMeta d.path (DFrac.own q)
      (some { m with size := pwSize m.size off.toNat (max j k), hi := max h (off.toNat + data.length) })
      by rw [pwSize_pwSize]; exact .rfl) $$ Hm
  ihave Hbs := (show osBytes (GF := GF) d.path (min off.toNat m.size) (DFrac.own 1)
        (ys.take (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)) ∗
      osBytes d.path (min off.toNat (pwSize m.size off.toNat j)) (DFrac.own 1)
        (pwBytes (pwSize m.size off.toNat j) off.toNat data k
          (ys.drop (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size))) ⊢
      osBytes d.path (min off.toNat m.size) (DFrac.own 1)
        (ys.take (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size) ++
          pwBytes (pwSize m.size off.toNat j) off.toNat data k
            (ys.drop (min off.toNat (pwSize m.size off.toNat j) - min off.toNat m.size))) by
    unfold osBytes
    refine BIBase.Entails.trans ?_ (bytesG_append _ _ _ _ _ _).2
    rw [hPl, show min off.toNat m.size + (min off.toNat (pwSize m.size off.toNat j) -
      min off.toNat m.size) = min off.toNat (pwSize m.size off.toNat j) by omega]) $$ [Hbs1 Hbs2]
  · iframe
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc := mcellsAny_merge m.maps (min off.toNat m.size)
    (min off.toNat (pwSize m.size off.toNat j)) (off.toNat + data.length) (by omega) (by omega)
    $$ [Hc1 Hc2]
  · iframe
  have hys' := pwBytes_retry m.size off.toNat data j k xs ys hj hk hxl hys
  have hj' : max j k ≤ data.length := by omega
  have hh' : m.hi ≤ max h (off.toNat + data.length) := by omega
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %(max j k) %_ %(max h (off.toNat + data.length)) %hj' %hys' %hh' Hm Hbs Hc Hosfd
      Hsl Hfd HΦ
  · rw [decide_eq_false he4]
    wp_auto
    have hsln : sl.len = W64 data.length := by
      apply BitVec.eq_of_toInt_eq
      simp only [sint.Z] at hslz
      rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
    rcases hke with ⟨rfl, rfl⟩ | he0
    · rw [decide_eq_true (by rw [hsln]; exact BitVec.zero_add _)]
      wp_auto
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      · ipureintro; exact ⟨hj', hys', hh', .inl ⟨by omega, hsln, rfl⟩⟩
    · have he0' : ¬ e = W64 0 := he0
      by_cases hkl : W64 0 + W64 ↑k = sl.len
      · rw [decide_eq_true hkl]
        wp_auto
        rw [decide_eq_false he0']
        wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hj', hys', hh', .inr ⟨rfl, by intro h; cases h⟩⟩
      · rw [decide_eq_false hkl]
        wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hj', hys', hh', .inr ⟨rfl, by intro h; cases h⟩⟩

end proof

end EtcdGrove
end Perennial
