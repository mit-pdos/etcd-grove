/-
The proof of `Spec/os/File__WriteAt.lean`: one attempt (`PWriteStart`, `PWriteFinish`) per
iteration of the model's loop, which retries only on `EINTR`, by Löb induction; the invariant is
the file as a write of the first `j` bytes left it (`pwPost_step`, `pwOut_step`).
-/
module

public import Proof.os.ErrorOk
public import Spec.os.File__WriteAt
public import Proof.os.File__WriteAtLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.WriteAt.wp_proof : os.File.WriteAt.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d m xs hwr hoff hgap hbig hn hn2 hxl
  have hmin0 : min off.toNat m.size = off.toNat := Nat.min_eq_left hgap
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
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  -- the invariant: the file as a write of the first `j` bytes left it, `nn ≤ j` of them written
  obtain ⟨nnv, hnnv⟩ : ∃ nnv : w64, nnv = W64 0 := ⟨_, rfl⟩
  conv in (occs := 4) (#(W64 0) : val) => rw [← hnnv]
  obtain ⟨mj, hmj⟩ : ∃ mj, mj = m := ⟨_, rfl⟩
  ihave Hm := (show osMeta (GF := GF) d.ino (DFrac.own 1) m ⊢ osMeta d.ino (DFrac.own 1) mj by
    rw [hmj]) $$ Hm
  obtain ⟨ys, hy⟩ : ∃ ys, ys = xs := ⟨_, rfl⟩
  ihave Hbs := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own 1) xs ⊢
    osBytes d.ino off.toNat (DFrac.own 1) ys by rw [hy]) $$ Hbs
  generalize hj0 : (0 : Nat) = j
  have hj : j ≤ data.length := by omega
  have hnn : nnv.toNat ≤ j := by subst hnnv; rw [← hj0]; decide
  have hnl : nnv.toNat < data.length := by
    subst hnnv; have : (W64 0).toNat = 0 := rfl
    omega
  have hinv : (j = 0 ∧ nnv.toNat = 0 ∧ mj = m ∧ ys = xs) ∨
      (mj = pwPost m off.toNat data.length j ∧ os.PwOut m off.toNat data j xs ys) :=
    .inl ⟨hj0.symm, by subst hnnv; rfl, hmj, hy⟩
  have hcj : PwCut off.toNat data.length j := by unfold PwCut; exact ⟨.inl hj0.symm, .inl hj0.symm⟩
  have hcn : nnv.toNat = 0 ∨ (off.toNat + nnv.toNat) % osPageSize = 0 := by
    left; subst hnnv; rfl
  clear hmj hy hj0 hnnv
  iloeb as IH generalizing %j %nnv %mj %ys %hnn %hnl %hj %hinv %hcj %hcn Hm Hbs Hc Hosfd Hsl Hfd HΦ
  -- one attempt, from `nn`
  have hnnz : sint.Z nnv = nnv.toNat := by
    simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  have hnnn : sint.nat nnv = nnv.toNat := by simp [sint.nat, hnnz]
  wp_auto
  have hmax : ¬ (sint.Z (W64 1073741824) < sint.Z (sl.len - nnv)) := by
    have hsub : sint.Z (sl.len - nnv) = sint.Z sl.len - sint.Z nnv := by
      have : sint.Z nnv ≤ sint.Z sl.len := by rw [hnnz, hslz]; omega
      have : 0 ≤ sint.Z nnv := by rw [hnnz]; omega
      word
    rw [hsub, hslz, hnnz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
  rw [decide_eq_false hmax]
  wp_auto
  have hsb : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
    rw [hnnz, hslz]; omega
  rw [if_pos hsb]
  ihave ⟨Hsl1, Hsl2⟩ := (ownSlice_split_all nnv sl dqs data ⟨by omega, by omega⟩).1 $$ Hsl
  rw [hnnn]
  wp_apply wp_bytes_to_string _ (data.drop nnv.toNat) dqs $$ Hsl2 as Hsl2
  ihave Hsl := (ownSlice_split_all nnv sl dqs data ⟨by omega, by omega⟩).2 $$ [Hsl1 Hsl2]
  · rw [hnnn]; iframe
  -- the bytes and cells this attempt takes
  have hmsz : mj.size = pwSize m.size off.toNat j := by
    rcases hinv with ⟨rfl, -, rfl, -⟩ | ⟨rfl, -⟩
    · simp [pwSize]
    · rfl
  have hmaps : mj.maps = m.maps := by
    rcases hinv with ⟨-, -, rfl, -⟩ | ⟨rfl, -⟩ <;> simp [pwPost]
  have hyl : ys.length = min (off.toNat + data.length) (pwSize m.size off.toNat j) - off.toNat := by
    rcases hinv with ⟨rfl, -, -, rfl⟩ | ⟨-, h⟩
    · simp [pwSize, hxl]
    · exact h.1
  have hS := pwSize_off m.size off.toNat j nnv.toNat hgap hnn
  have hnny : nnv.toNat ≤ ys.length := by rw [hyl]; omega
  ihave ⟨Hbs1, Hbs2⟩ := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own 1) ys ⊢
      osBytes d.ino off.toNat (DFrac.own 1) (ys.take nnv.toNat) ∗
      osBytes d.ino (off.toNat + nnv.toNat) (DFrac.own 1) (ys.drop nnv.toNat) by
    conv => lhs; rw [← List.take_append_drop nnv.toNat ys]
    unfold osBytes
    refine (bytesG_append _ _ _ _ _ _).1.trans ?_
    rw [List.length_take, Nat.min_eq_left hnny]) $$ Hbs
  ihave ⟨Hc1, Hc2⟩ := mcellsAny_split m.maps off.toNat (off.toNat + nnv.toNat)
    (off.toNat + data.length) (by omega) (by omega) $$ Hc
  have hoffv : (off + nnv).toNat = off.toNat + nnv.toNat := by
    rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
  have hoffv' : 0 ≤ (off + nnv).toInt := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hoffv]; omega)]; omega
  have hminS : min (off.toNat + nnv.toNat) (pwSize m.size off.toNat j) = off.toNat + nnv.toNat :=
    Nat.min_eq_left hS
  have hdl : (data.drop nnv.toNat).length = data.length - nnv.toNat := List.length_drop
  have hdne : data.drop nnv.toNat ≠ [] := by
    intro h; have := congrArg List.length h; rw [hdl] at this; simp at this; omega
  have hend : off.toNat + nnv.toNat + (data.length - nnv.toNat) = off.toNat + data.length := by
    omega
  wp_apply wp_osPWriteStart fd (off + nnv) (data.drop nnv.toNat) dq d mj (ys.drop nnv.toNat)
    CoPset.subseteq_top hwr hoffv' (by rw [hoffv, hmsz]; exact hS) hdne
    (by rw [hoffv, hdl, List.length_drop, hyl, hmsz, hend]; omega)
    $$ Hinv Hosfd Hm [Hbs2] [Hc2] as %t %nst %- Hosfd Ht
  · rw [hoffv]; iexact Hbs2
  · rw [hoffv, hdl, hend, hmaps]; iexact Hc2
  wp_apply wp_osPWriteFinish t d.ino (off + nnv).toNat (data.drop nnv.toNat) mj
    (ys.drop nnv.toNat) nst CoPset.subseteq_top $$ Hinv Ht as %k %e %zs %hke %hpc Hm Hbs2 Hc2
  obtain ⟨hk, hke, -, -⟩ := hke
  rw [hdl] at hk
  have hpc' : PwCut (off.toNat + nnv.toNat) (data.length - nnv.toNat) k := by
    rw [hoffv, hdl] at hpc; exact hpc
  have hcj' : PwCut off.toNat data.length (max j (nnv.toNat + k)) :=
    pwCut_step _ _ _ _ _ hcj hnn hcn hk hnl hpc'
  -- the file as a write of the first `max j (nn + k)` bytes left it
  have hmeta : pwPost mj (off + nnv).toNat (data.drop nnv.toNat).length k =
      pwPost m off.toNat data.length (max j (nnv.toNat + k)) := by
    rw [hoffv, hdl]
    rcases hinv with ⟨rfl, h0, rfl, -⟩ | ⟨rfl, -⟩
    · rw [h0]; simp
    · exact pwPost_step m off.toNat data.length nnv.toNat j k hgap hnn hj hnl hk
  ihave Hm := (show osMeta (GF := GF) d.ino (DFrac.own 1)
      (pwPost mj (off + nnv).toNat (data.drop nnv.toNat).length k) ⊢
    osMeta d.ino (DFrac.own 1) (pwPost m off.toNat data.length (max j (nnv.toNat + k)))
      by rw [hmeta]) $$ Hm
  ihave Hbs := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own 1) (ys.take nnv.toNat) ∗
      osBytes d.ino (off + nnv).toNat (DFrac.own 1)
        (pwBytes mj.size (off + nnv).toNat (data.drop nnv.toNat) k nst (ys.drop nnv.toNat) zs) ⊢
      osBytes d.ino off.toNat (DFrac.own 1)
        (ys.take nnv.toNat ++ pwBytes (pwSize m.size off.toNat j) (off.toNat + nnv.toNat)
          (data.drop nnv.toNat) k nst (ys.drop nnv.toNat) zs) by
    rw [hoffv, hmsz]
    unfold osBytes
    refine BIBase.Entails.trans ?_ (bytesG_append _ _ _ _ _ _).2
    rw [List.length_take, Nat.min_eq_left hnny]) $$ [Hbs1 Hbs2]
  · iframe
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc := mcellsAny_merge m.maps off.toNat (off.toNat + nnv.toNat) (off.toNat + data.length)
    (by omega) (by omega) $$ [Hc1 Hc2]
  · rw [hoffv, hdl, hend, hmaps]; iframe
  have hys' := pwOut_step m off.toNat nnv.toNat data j k nst xs ys zs hgap hnn hj hk hxl
    (by rcases hinv with ⟨h1, h2, -, h3⟩ | ⟨-, h⟩
        · exact .inl ⟨h1, h2, h3⟩
        · exact .inr h)
  have hj' : max j (nnv.toNat + k) ≤ data.length := by omega
  have hsln : sl.len = W64 data.length := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.Z] at hslz
    rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %(max j (nnv.toNat + k)) %nnv %_ %_ %(by omega) %hnl %hj' %(.inr ⟨rfl, hys'⟩)
      %hcj' %hcn Hm Hbs Hc Hosfd Hsl Hfd HΦ
  · rw [decide_eq_false he4]
    wp_auto
    have hWk : (W64 k).toNat = k := by
      simp only [W64]; rw [BitVec.toNat_ofInt]; omega
    have hnk : (nnv + W64 k).toNat = nnv.toNat + k := by
      rw [BitVec.toNat_add, hWk]; exact Nat.mod_eq_of_lt (by omega)
    by_cases hfull : nnv + W64 k = sl.len
    · rw [decide_eq_true hfull]
      wp_auto
      have hfk : nnv.toNat + k = data.length := by
        have := congrArg BitVec.toNat hfull; rw [hnk, hsln] at this
        simp only [W64] at this; rw [BitVec.toNat_ofInt] at this; omega
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        wp_auto
        ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hj', hys', hcj', .inl ⟨by omega, hsln, rfl⟩⟩
      · rw [decide_eq_false he0]
        wp_auto
        simp only [decide_eq_false he0, Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0 $$ Hn as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hj', hys', hcj', .inr ⟨rfl, by intro h; cases h⟩⟩
    · rw [decide_eq_false hfull]
      wp_auto
      by_cases he0 : e = W64 0
      · -- a short write: the next attempt from `nn + k`
        rw [decide_eq_true he0]
        simp only [Bool.not_true]
        wp_pure
        have hk0 : 0 < k := by
          rcases hke with ⟨hkk | hkk, -⟩ | hne
          · have : nnv.toNat + k ≠ data.length := by
              intro hc; apply hfull; apply BitVec.eq_of_toNat_eq
              rw [hnk, hsln]; simp only [W64]; rw [BitVec.toNat_ofInt]; omega
            omega
          · exact hkk
          · exact absurd he0 hne
        have hnl' : (nnv + W64 k).toNat < data.length := by
          rw [hnk]
          have : nnv.toNat + k ≠ data.length := by
            intro hc; apply hfull; apply BitVec.eq_of_toNat_eq
            rw [hnk, hsln]; simp only [W64]; rw [BitVec.toNat_ofInt]; omega
          omega
        have hcn' : (nnv + W64 k).toNat = 0 ∨ (off.toNat + (nnv + W64 k).toNat) % osPageSize = 0 := by
          rw [hnk]
          exact pwCut_short _ _ _ _ hk0 (by rw [hnk] at hnl'; omega) hpc' hk
        iapply IH $$ %(max j (nnv.toNat + k)) %(nnv + W64 k) %_ %_ %(by rw [hnk]; omega) %hnl'
          %hj' %(.inr ⟨rfl, hys'⟩) %hcj' %hcn' [Hm] [Hbs] [Hc] Hosfd Hsl Hfd HΦ
        · iexact Hm
        · iexact Hbs
        · iexact Hc
      · rw [decide_eq_false he0]
        simp only [Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0 $$ Hn as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hj', hys', hcj', .inr ⟨rfl, by intro h; cases h⟩⟩

end proof

end EtcdGrove
end Perennial
