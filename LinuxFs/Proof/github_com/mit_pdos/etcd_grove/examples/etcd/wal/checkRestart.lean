/- Lean-first (no Rocq counterpart). The proof of `checkRestart`. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.checkRestart
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.copyOps
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walImgs
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.openBound
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walReadCut
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.contentsEq
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.addCand
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.CandsLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem val_decide_true {P : Prop} [Decidable P] (h : (#(decide P) : val) = #true) : P := by
  have := GoGlobalContext.intoVal_inj_bool h
  simpa using this

theorem val_decide_false {P : Prop} [Decidable P] (h : ¬ (#(decide P) : val) = #true) : ¬ P := by
  intro hp; apply h; simp [hp]

set_option maxHeartbeats 4000000 in
theorem checkRestart.wp_proof (wp_copyOps : copyOps.spec (GF := GF) (hG := hG))
    (wp_walImgs : walImgs.spec (GF := GF) (hG := hG))
    (wp_openBound : openBound.spec (GF := GF) (hG := hG))
    (wp_walReadCut : walReadCut.spec (GF := GF) (hG := hG))
    (wp_contentsEq : contentsEq.spec (GF := GF) (hG := hG))
    (wp_addCand : addCand.spec (GF := GF) (hG := hG)) :
    checkRestart.spec (GF := GF) (hG := hG) := by
  intro vo vc o c hwf hne
  wp_start as ⟨Ho, #Hc⟩
  iunfold oracleRep at Ho
  icases Ho with ⟨%Hof, Hcands, #Hsince, Hsincecap, #Hopens, Hopenscap⟩
  iunfold candsOwn at Hcands
  icases Hcands with ⟨%cvs, Hcs, Hcscap, #Hcel⟩
  ihave %Hcslen := ownSlice_len $$ Hcs
  ihave %Hcel_len := candsElems_length $$ Hcel
  ihave %Hsl := (show opsRep (GF := GF) vo.since' o.since ⊢ ⌜(∃ svs : List walOp, svs.length = o.since.length ∧ svs.length = sint.nat vo.since'.len)⌝ from by
    iintro H
    iunfold opsRep at H
    icases H with ⟨%svs, Hs, Hel⟩
    ihave %h1 := ownSlice_len $$ Hs
    ihave %h2 := opsElems_length $$ Hel
    ipureintro; exact ⟨svs, h2, h1.1⟩) $$ Hsince
  ihave %Hol := ownSlice_len $$ Hopens
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := cand) (W64 0)) as %n0 ⟨Hn0, Hn0cap⟩
  · ipureintro; word
  simp only [List.replicate_zero]
  wp_auto
  ihave HI : (∃ (ci : w64) (nx : GoSlice),
      "ci" ∷ ci_ptr ↦ ci ∗ "next" ∷ next_ptr ↦ nx ∗
      "Hnx" ∷ candsOwn nx ((o.cands.take (sint.nat ci)).foldl (tCandNext o c) []) ∗
      "Hcs" ∷ vo.cands' ↦* cvs ∗
      "%Hci" ∷ ⌜0 ≤ sint.Z ci ∧ sint.Z ci ≤ sint.Z vo.cands'.len⌝ : IProp GF)
      $$ [ci next Hn0 Hn0cap Hcs]
  · iexists W64 0, n0
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.take_zero, List.foldl_nil]
    iframe
    isplitl
    · iunfold candsOwn
      iexists []
      iframe
      iunfold candsElems
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %c' %h
      simp at h
    · ipureintro; constructor <;> word
  wp_for HI
  by_cases hlt : sint.Z ci < sint.Z vo.cands'.len
  · rw [if_pos (by simp [hlt])]
    have hcil : sint.nat ci < cvs.length := by
      have : sint.nat ci < sint.nat vo.cands'.len := by word
      omega
    obtain ⟨cv, Hcv⟩ : ∃ cv, cvs[sint.nat ci]? = some cv := ⟨_, List.getElem?_eq_getElem hcil⟩
    have hb : 0 ≤ sint.Z ci ∧ sint.Z ci < sint.Z vo.cands'.len := ⟨Hci.1, hlt⟩
    icases candsElems_lookup cvs o.cands (sint.nat ci) cv Hcv $$ Hcel with ⟨%cd, %Hcd, #Hcdr⟩
    iunfold candRep at Hcdr
    icases Hcdr with ⟨%Hcdf, #Hcdh⟩
    icases ownSlice_elem_read_cand (sint.Z ci) cv vo.cands' cvs Hci.1 (by simpa [sint.nat] using Hcv) $$ Hcs
      with ⟨Hcv, Hcsback⟩
    wp_auto
    iterate 4 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    ihave Hcs := Hcsback $$ Hcv
    wp_apply (wp_copyOps cv.h' cd.h) as %hs ⟨%hvs, Hh, Hhcap, #Hhel⟩
    · iexact Hcdh
    ihave Hsince2 := Hsince
    iunfold opsRep at Hsince2
    icases Hsince2 with ⟨%svs, #Hsv, #Hsvel⟩
    ihave %Hsvl := ownSlice_len $$ Hsv
    ihave %Hsvel_len := opsElems_length $$ Hsvel
    ihave HI2 : (∃ (i : w64) (hs' : GoSlice) (hvs' : List walOp),
        "i" ∷ i_ptr ↦ i ∗ "h" ∷ h_ptr ↦ hs' ∗ "Hh" ∷ hs' ↦* hvs' ∗
        "Hhcap" ∷ ownSliceCap walOp hs' (DFrac.own 1) ∗
        "Hhel" ∷ opsElems hvs' (cd.h ++ o.since.take (sint.nat i)) ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z vo.since'.len⌝ : IProp GF) $$ [i h Hh Hhcap]
    · iexists W64 0, hs, hvs
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp only [List.take_zero, List.append_nil]
      iframe
      isplitl []
      · iexact Hhel
      ipureintro; constructor <;> word
    wp_for HI2
    icases Hhel with #Hhel
    by_cases hlt2 : sint.Z i < sint.Z vo.since'.len
    · rw [if_pos (by simp [hlt2])]
      have hil : sint.nat i < svs.length := by
        have : sint.nat i < sint.nat vo.since'.len := by word
        omega
      obtain ⟨sv, Hsvi⟩ : ∃ sv, svs[sint.nat i]? = some sv := ⟨_, List.getElem?_eq_getElem hil⟩
      have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z vo.since'.len := ⟨Hi.1, hlt2⟩
      icases ownSlice_elem_acc (sint.Z i) sv vo.since' DFrac.discard svs Hi.1
        (by simpa [sint.nat] using Hsvi) $$ Hsv with ⟨Hsvv, -⟩
      icases opsElems_lookup svs o.since (sint.nat i) sv Hsvi $$ Hsvel with ⟨%op, %Hop, #Hopr⟩
      wp_auto
      iterate 4 (try simp only [hb2, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      wp_apply wp_slice_append $$ [$Hh $Hhcap $Hosl] as %hs2 ⟨Hh2, Hhcap2, -⟩
      ihave Hhel2 := opsElems_snoc hvs' _ sv op $$ [$Hhel $Hopr]
      wp_for_post
      iframe
      iexists i + W64 1, hs2, (hvs' ++ [sv])
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hi1, List.take_add_one, Hop]
      simp only [Option.toList_some, List.append_assoc]
      iframe
      ipureintro; constructor <;> word
    · simp only [hlt2, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hin2 : sint.nat i = o.since.length := by
        have : sint.nat i = sint.nat vo.since'.len := by word
        omega
      have hH : cd.h ++ List.take (sint.nat i) o.since = tCandHist o cd := by
        rw [hin2, List.take_length]; rfl
      rw [hH]
      wp_auto
      ihave Hcdh2 := Hcdh
      iunfold opsRep at Hcdh2
      icases Hcdh2 with ⟨%cdvs, #Hcdv, #Hcdvel⟩
      ihave %Hcdvl := ownSlice_len $$ Hcdv
      ihave %Hcdvel_len := opsElems_length $$ Hcdvel
      have hcdm : cd ∈ o.cands := List.mem_of_getElem? Hcd
      obtain ⟨hwfh, hlen62⟩ := hwf.2 cd hcdm
      have hhl : (tCandHist o cd).length = cd.h.length + o.since.length := by
        simp [tCandHist]
      have hsy : uint.nat vo.synced' = uint.nat o.synced := by rw [Hof.2.1]
      have hn : sint.nat (cv.h'.len + vo.synced') = tCandMark o cd ∧ 0 ≤ sint.Z (cv.h'.len + vo.synced') := by
        unfold tCandMark
        have := hwf.1
        constructor <;> word
      imod ownSlice_persist $$ Hh with #Hh
      wp_apply (wp_walImgs hs' (tCandHist o cd) (cv.h'.len + vo.synced') hn.2) as %is #Himgs
      · iunfold opsRep; iexists hvs'; isplitl []
        · iexact Hh
        · iexact Hhel
      rw [hn.1]
      rw [Hcdf.1]
      ihave HI3 : (∃ (si : w64),
          "si" ∷ si_ptr ↦ si ∗
          "unl" ∷ unl_ptr ↦ tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) (o.opens.take (sint.nat si)) cd.unl ∗
          "%Hsi" ∷ ⌜0 ≤ sint.Z si ∧ sint.Z si ≤ sint.Z vo.opens'.len⌝ : IProp GF) $$ [si unl]
      · iexists W64 0
        rw [show sint.nat (W64 0) = 0 from rfl]
        simp only [List.take_zero, tRaiseUnl, List.foldl_nil]
        iframe
        ipureintro; constructor <;> word
      wp_for HI3
      by_cases hlt3 : sint.Z si < sint.Z vo.opens'.len
      · rw [if_pos (by simp [hlt3])]
        have hsl : sint.nat si < o.opens.length := by
          have : sint.nat si < sint.nat vo.opens'.len := by word
          omega
        obtain ⟨op, Hop⟩ : ∃ op, o.opens[sint.nat si]? = some op := ⟨_, List.getElem?_eq_getElem hsl⟩
        have hb3 : 0 ≤ sint.Z si ∧ sint.Z si < sint.Z vo.opens'.len := ⟨Hsi.1, hlt3⟩
        icases ownSlice_elem_acc (sint.Z si) op vo.opens' DFrac.discard o.opens Hsi.1
          (by simpa [sint.nat] using Hop) $$ Hopens with ⟨Hopv, -⟩
        wp_auto
        iterate 4 (try simp only [hb3, _root_.and_self, ↓reduceIte]; try wp_auto)
        wp_apply (wp_openBound is (tImgs (tCandHist o cd) (tCandMark o cd)) op)
        · iexact Himgs
        have hsi1 : sint.nat (si + W64 1) = sint.nat si + 1 := by word
        have hstep := foldl_take_succ
          (fun u s => if uint.nat u < uint.nat (tOpenBound (tImgs (tCandHist o cd) (tCandMark o cd)) s) then
            tOpenBound (tImgs (tCandHist o cd) (tCandMark o cd)) s else u)
          cd.unl o.opens (sint.nat si) op Hop
        wp_if_destruct
        · wp_for_post
          iframe
          iexists si + W64 1
          unfold tRaiseUnl at *
          rw [hsi1, hstep, if_pos (by word)]
          iframe
          ipureintro; constructor <;> word
        · wp_for_post
          iframe
          iexists si + W64 1
          unfold tRaiseUnl at *
          rw [hsi1, hstep, if_neg (by word)]
          iframe
          ipureintro; constructor <;> word
      · simp only [hlt3, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hin3 : sint.nat si = o.opens.length := by
          have : sint.nat si = sint.nat vo.opens'.len := by word
          omega
        rw [hin3, List.take_length]
        wp_auto
        ihave Himgs2 := Himgs
        iunfold imgsRep at Himgs2
        icases Himgs2 with ⟨%ivs, #Hiv, #Hivel⟩
        ihave %Hivl := ownSlice_len $$ Hiv
        ihave %Hivel_len := imgsElems_length $$ Hivel
        ihave HI4 : (∃ (k : w64) (nx' : GoSlice),
            "k" ∷ k_ptr ↦ k ∗ "next" ∷ next_ptr ↦ nx' ∗
            "Hnx" ∷ candsOwn nx' (((tImgs (tCandHist o cd) (tCandMark o cd)).take (sint.nat k)).foldl
              (fun nx img => if tImgReads img cd.pur c then
                tAddCand img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur nx
                else nx) ((o.cands.take (sint.nat ci)).foldl (tCandNext o c) [])) ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z is.len⌝ : IProp GF) $$ [k next Hnx]
        · iexists W64 0, nx
          rw [show sint.nat (W64 0) = 0 from rfl]
          simp only [List.take_zero, List.foldl_nil]
          iframe
          ipureintro; constructor <;> word
        wp_for HI4
        by_cases hlt4 : sint.Z k < sint.Z is.len
        · rw [if_pos (by simp [hlt4])]
          have hkl : sint.nat k < ivs.length := by
            have : sint.nat k < sint.nat is.len := by word
            omega
          obtain ⟨iv, Hivk⟩ : ∃ iv, ivs[sint.nat k]? = some iv := ⟨_, List.getElem?_eq_getElem hkl⟩
          have hb4 : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z is.len := ⟨Hk.1, hlt4⟩
          icases ownSlice_elem_acc (sint.Z k) iv is DFrac.discard ivs Hk.1
            (by simpa [sint.nat] using Hivk) $$ Hiv with ⟨Hivv, -⟩
          icases imgsElems_lookup ivs _ (sint.nat k) iv Hivk $$ Hivel with ⟨%img, %Himg, #Himgr⟩
          ihave Himgr2 := Himgr
          iunfold opsRep at Himgr2
          icases Himgr2 with ⟨%imvs, #Himv, #Himvel⟩
          ihave %Himvl := ownSlice_len $$ Himv
          ihave %Himvel_len := opsElems_length $$ Himvel
          have himgm : img ∈ tImgs (tCandHist o cd) (tCandMark o cd) := List.mem_of_getElem? Himg
          have himgwf : tHistWf img := tHistWf_of_mem_tImgs hwfh himgm
          wp_auto
          iterate 4 (try simp only [hb4, _root_.and_self, ↓reduceIte]; try wp_auto)
          rw [Hcdf.2]
          wp_if_destruct
          all_goals
            iterate 3 (try simp only [hb4, _root_.and_self, ↓reduceIte]; try wp_auto)
          all_goals
            ihave Hkm : (∃ km : w64, kmax_ptr ↦ km ∗
                ⌜uint.nat km = min (uint.nat cd.pur) img.length⌝ : IProp GF) $$ [kmax]
            · iexists _
              iframe
              ipureintro
              have := Hif
              rw [Nat.min_def]
              split <;> word
            icases Hkm with ⟨%km, kmax, %Hkm⟩
          all_goals
            have himl : img.length = sint.nat iv.len := by omega
            have hkmb : uint.nat km ≤ img.length := by rw [Hkm]; exact Nat.min_le_right _ _
            have himl63 : img.length < 2 ^ 63 := by have := Himvl.2; word
            have hstep := foldl_take_succ
              (fun nx img => if tImgReads img cd.pur c = true then
                tAddCand img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur nx
                else nx)
              ((o.cands.take (sint.nat ci)).foldl (tCandNext o c) [])
              (tImgs (tCandHist o cd) (tCandMark o cd)) (sint.nat k) img Himg
            have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
            ihave HI5 : (∃ (kk : w64),
                "kk" ∷ kk_ptr ↦ kk ∗
                "%Hkk" ∷ ⌜uint.nat kk ≤ uint.nat km + 1 ∧
                  ∀ j, j < uint.nat kk → tReadCut img (W64 j) ≠ some c⌝ : IProp GF) $$ [kk]
            · iexists W64 0
              iframe
              ipureintro
              refine ⟨by word, fun j hj => ?_⟩
              rw [show uint.nat (W64 0) = 0 from rfl] at hj; omega
            wp_for HI5
            wp_if_destruct
            · iterate 3 (try simp only [hb4, _root_.and_self, ↓reduceIte]; try wp_auto)
              have hkkle : uint.nat kk ≤ uint.nat km := by
                first | (have := Hif; word) | (have := val_decide_true Hif; word)
              have hkk1 : uint.nat (kk + W64 1) = uint.nat kk + 1 := by word
              have hWkk : (W64 (uint.nat kk : Int) : w64) = kk := by word
              wp_apply (wp_walReadCut iv img kk himgwf (by omega)) as %rc %ok Hres
              · iexact Himgr
              cases hr : tReadCut img kk with
              | none =>
                iunfold readRes at Hres
                icases Hres with %hok
                subst hok
                wp_auto
                wp_for_post
                iframe
                iexists kk + W64 1
                iframe
                ipureintro
                refine ⟨by word, fun j hj => ?_⟩
                rw [hkk1] at hj
                by_cases hjk : j < uint.nat kk
                · exact Hkk.2 j hjk
                · have : j = uint.nat kk := by omega
                  subst this; rw [hWkk, hr]; simp
              | some c' =>
                iunfold readRes at Hres
                icases Hres with ⟨%hok, #Hrc⟩
                subst hok
                wp_auto
                wp_apply (wp_contentsEq rc vc c' c)
                · isplitr
                  · iexact Hrc
                  · iexact Hc
                wp_if_destruct
                · subst Hif
                  iterate 3 (try simp only [hb4, _root_.and_self, ↓reduceIte]; try wp_auto)
                  rw [Hcdf.2]
                  wp_apply (wp_addCand nx' iv _ img
                    (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur) $$ [Hnx]
                    as %nx2 Hnx2
                  · iframe
                    iexact Himgr
                  wp_for_post
                  wp_for_post
                  iframe
                  iexists k + W64 1, nx2
                  have hreads : tImgReads img cd.pur c' = true :=
                    tImgReads_true (kk := uint.nat kk) ⟨by omega, by omega⟩ (by rw [hWkk, hr])
                  rw [hk1, hstep, if_pos hreads]
                  iframe
                  ipureintro; constructor <;> word
                · wp_for_post
                  iframe
                  iexists kk + W64 1
                  iframe
                  ipureintro
                  refine ⟨by word, fun j hj => ?_⟩
                  rw [hkk1] at hj
                  by_cases hjk : j < uint.nat kk
                  · exact Hkk.2 j hjk
                  · have : j = uint.nat kk := by omega
                    subst this; rw [hWkk, hr]; simpa using Hif
            · have hnot : ¬ uint.Z kk ≤ uint.Z km := by
                first | exact Hif | exact val_decide_false Hif
              try rw [if_pos (by simp [hnot])]
              wp_for_post
              iframe
              iexists k + W64 1, nx'
              have hreads : tImgReads img cd.pur c = false := by
                apply tImgReads_false
                intro j hj
                rw [← Hkm] at hj
                exact Hkk.2 j (by have := hnot; word)
              rw [hk1, hstep, if_neg (by rw [hreads]; simp)]
              iframe
              ipureintro; constructor <;> word
        · simp only [hlt4, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hin4 : sint.nat k = (tImgs (tCandHist o cd) (tCandMark o cd)).length := by
            have : sint.nat k = sint.nat is.len := by word
            omega
          rw [hin4, List.take_length]
          wp_for_post
          iframe
          iexists ci + W64 1, nx'
          have hci1 : sint.nat (ci + W64 1) = sint.nat ci + 1 := by word
          rw [hci1, foldl_take_succ (tCandNext o c) [] o.cands (sint.nat ci) cd Hcd]
          unfold tCandNext
          iframe
          ipureintro; constructor <;> word
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hin : sint.nat ci = o.cands.length := by
      have : sint.nat ci = sint.nat vo.cands'.len := by word
      omega
    rw [hin, List.take_length]
    iunfold candsOwn at Hnx
    icases Hnx with ⟨%nvs, Hn, Hncap, #Hnel⟩
    ihave %Hnl := ownSlice_len $$ Hn
    ihave %Hnel_len := candsElems_length $$ Hnel
    wp_auto
    wp_if_destruct
    · exfalso; apply hne
      apply List.eq_nil_of_length_eq_zero
      unfold tCheckNext
      have : nvs.length = 0 := by word
      omega
    wp_apply +noauto (wp_slice_make2 (V := walOp) (W64 0)) as %s0 ⟨Hs0, Hs0cap⟩
    · ipureintro; word
    simp only [List.replicate_zero]
    imod ownSlice_persist $$ Hs0 with #Hs0
    wp_auto
    wp_apply +noauto (wp_slice_make2 (V := w64) (W64 0)) as %p0 ⟨Hp0, Hp0cap⟩
    · ipureintro; word
    simp only [List.replicate_zero]
    imod ownSlice_persist $$ Hp0 with #Hp0
    wp_auto
    iapply HΦ
    isplitl [Hsincecap Hopenscap Hcscap Hcs]
    · iunfold oracleRep
      isplitr
      · ipureintro; exact Hof
      isplitl [Hcscap Hcs]
      · iunfold candsOwn
        iexists cvs
        iframe
        iexact Hcel
      iframe
      isplitl []
      · iexact Hsince
      · iexact Hopens
    · iunfold oracleRep
      simp only [tCheckRestart]
      iunfold contentsRep at Hc
      icases Hc with ⟨%Hcf, -⟩
      isplitr
      · ipureintro; refine ⟨?_, ?_, ?_⟩ <;> first | trivial | exact Hcf.1 | rfl
      isplitl [Hn Hncap]
      · iunfold candsOwn
        iexists nvs
        iframe
        unfold tCheckNext
        iexact Hnel
      isplitl []
      · iunfold opsRep
        iexists []
        isplitl []
        · iexact Hs0
        iapply opsElems_nil
      iframe
      iexact Hp0
