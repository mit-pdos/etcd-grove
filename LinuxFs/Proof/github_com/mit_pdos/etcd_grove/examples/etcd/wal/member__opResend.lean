/- Lean-first (no Rocq counterpart). The proof of `member.opResend`. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opResend
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.copyOps
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walFold
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__hs
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__save
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.CandsLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

set_option hygiene false in
/-- `opResend`'s early returns: nothing done. Unhygienic: it names the proof's hypotheses. -/
local macro "resend_nop" : tactic => `(tactic| (
  iapply HΦ
  iframe
  ileft
  isplitr
  · ipureintro; rfl
  iframe
  iunfold memSaveRes
  iframe
  iframe H1 H2 H3 H4 H13 H15 H16))

set_option hygiene false in
/-- `opResend` after the entries' loop (its three exits): the empty check, the terms' loop, the last
index, `save`. Unhygienic: it names the proof's hypotheses. -/
local macro "resend_rest" : tactic => `(tactic| (
  have hesw : ∀ x ∈ es, tEntWf x := fun x hx => hentwf x (Hi.2.2.2 x hx)
  imod ownSlice_persist $$ Hes with #Hes
  ihave %Hesl := ownSlice_len $$ Hes
  try wp_auto
  wp_if_destruct
  · resend_nop
  have hesl : 1 ≤ es.length ∧ es.length ≤ 3 := by
    constructor
    · have : esl.len ≠ W64 0 := by assumption
      rw [Hesl.1]; word
    · omega
  ihave HI2 : (∃ (j t' : w64) (M' : GMap w64 w64),
      "i" ∷ i_ptr ↦ j ∗ "Ht" ∷ m.[member, go!"term"] ↦ t' ∗ "HM" ∷ tm ↦$ M' ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z esl.len ∧ (tMemFields t M → tMemFields t' M')⌝ : IProp GF)
      $$ [i Ht HM]
  · iexists W64 0, t, M
    iframe
    ipureintro
    exact ⟨by word, by word, id⟩
  wp_for HI2
  by_cases hlt : sint.Z j < sint.Z esl.len
  · rw [if_pos (by simp [hlt])]
    have hjl : sint.nat j < es.length := by
      have : sint.nat j < sint.nat esl.len := by word
      omega
    obtain ⟨x, Hx⟩ : ∃ x, es[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hxw : tEntWf x := hesw x (List.mem_of_getElem? Hx)
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z esl.len := ⟨Hj.1, hlt⟩
    icases ownSlice_elem_acc (sint.Z j) x esl DFrac.discard es Hj.1
      (by simpa [sint.nat] using Hx) $$ Hes with ⟨Hxv, -⟩
    icases typedPointsto_split _ _ _ $$ Hxv with Hxv
    simp only [TypedPointsto.typedPointstoDef]
    icases Hxv with ⟨#Hxi, #Hxt, #Hxs, #Hxa, -⟩
    wp_auto
    iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    wp_if_destruct
    all_goals
      iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_apply (wp_mapInsert go.uint64 tm M' x.index' x.term') $$ [HM] as HM
      · iexact HM
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, _, <[x.index' := x.term']> M'
      iframe
      ipureintro
      refine ⟨by word, by word, fun hf0 => ?_⟩
      have hf1 := Hj.2.2 hf0
      refine ⟨?_, tTermsOk_insert hf1.2 _ _ hxw.2.2.2⟩
      first | exact hxw.2.2.2 | exact hf1.1
  · simp only [hlt, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte, val_false_ne_true,
  not_false_eq_true]
    have hjn : sint.nat j = es.length := by
      have : sint.nat j = sint.nat esl.len := by word
      omega
    obtain ⟨x, Hx⟩ : ∃ x, es[es.length - 1]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hb : 0 ≤ sint.Z (esl.len - W64 1) ∧ sint.Z (esl.len - W64 1) < sint.Z esl.len := by
      constructor <;> word
    icases ownSlice_elem_acc (sint.Z (esl.len - W64 1)) x esl DFrac.discard es hb.1
      (by
        have : (sint.Z (esl.len - W64 1)).toNat = es.length - 1 := by word
        rw [this]; exact Hx) $$ Hes with ⟨Hxv, -⟩
    icases typedPointsto_split _ _ _ $$ Hxv with Hxv
    simp only [TypedPointsto.typedPointstoDef]
    icases Hxv with ⟨#Hxi, #Hxt, #Hxs, #Hxa, -⟩
    wp_auto
    iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    wp_apply (wp_hs m t' vo cm) $$ [Ht Hv Hc] as ⟨Ht, Hv, Hc⟩
    · iframe
    try wp_auto
    wp_apply (wp_save W e γ m w v o os c d qc (hardState.mk t' vo cm) esl es hf hok hhs
      hesw (tOrRoom_save hroom (by omega) _).1 (tOrRoom_save hroom (by omega) _).2)
      $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14] as %b Hpost
    · iframe
      iframe Hes H13 H15 H16 H1 H2 H3 H4
    iapply HΦ
    iframe
    iright
    iexists t', _, es, M'
    unfold memSavePost
    iframe
    ipureintro
    exact ⟨hesl.1, hesl.2, hesw, Hj.2.2⟩))

set_option maxHeartbeats 1000000 in
theorem member.opResend.wp_proof (wp_copyOps : copyOps.spec (GF := GF) (hG := hG))
    (wp_walFold : walFold.spec (GF := GF) (hG := hG))
    (wp_hs : member.hs.spec (GF := GF) (hG := hG)) (wp_save : member.save.spec (GF := GF) (hG := hG)) :
    member.opResend.spec (GF := GF) (hG := hG) := by
  intro W e γ m w v o os c d qc t vo cm l tm M hf hok hhs hwf hroom
  wp_start as ⟨Hres, Ht, Hv, Hc, Hl, Htm, HM⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe
    ileft
    iframe
    ipureintro; rfl
  iunfold memSaveRes at Hres
  icases Hres with ⟨#H1, #H2, #H3, #H4, H5, H6, H7, H8, H9, Hrep, H11, H12, #H13, H14, #H15, #H16⟩
  iunfold oracleRep at Hrep
  icases Hrep with ⟨%Hof, Hcands, #Hsince, Hsincecap, #Hopens, Hopenscap⟩
  iunfold candsOwn at Hcands
  icases Hcands with ⟨%cvs, Hcs, Hcscap, #Hcel⟩
  ihave %Hcslen := ownSlice_len $$ Hcs
  ihave %Hcel_len := candsElems_length $$ Hcel
  have hc0 : 0 < cvs.length := by
    rw [Hcel_len]; exact List.length_pos_of_mem hok.2.1
  obtain ⟨cv, Hcv⟩ : ∃ cv, cvs[0]? = some cv := ⟨_, List.getElem?_eq_getElem hc0⟩
  icases candsElems_lookup cvs o.cands 0 cv Hcv $$ Hcel with ⟨%cd, %Hcd, #Hcdr⟩
  iunfold candRep at Hcdr
  icases Hcdr with ⟨%Hcdf, #Hcdh⟩
  icases ownSlice_elem_read_cand (sint.Z (W64 0)) cv v.cands' cvs (by decide) (by simpa using Hcv) $$ Hcs
    with ⟨Hcv, Hcsback⟩
  wp_auto
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z v.cands'.len := by
    constructor
    · decide
    · have := Hcslen.1; word
  iterate 4 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
  ihave Hcs := Hcsback $$ Hcv
  wp_apply (wp_copyOps cv.h' cd.h) as %hs ⟨%hvs, Hh, Hhcap, #Hhel⟩
  · iexact Hcdh
  ihave Hrep : oracleRep v o $$ [Hcs Hcscap Hsincecap Hopenscap]
  · iunfold oracleRep
    iframe
    isplitr
    · ipureintro; exact Hof
    isplitl
    · iunfold candsOwn; iexists cvs; iframe; iexact Hcel
    · iframe #
  ihave Hsince2 := Hsince
  iunfold opsRep at Hsince2
  icases Hsince2 with ⟨%svs, #Hsv, #Hsvel⟩
  ihave %Hsvl := ownSlice_len $$ Hsv
  ihave %Hsvel_len := opsElems_length $$ Hsvel
  ihave HI2 : (∃ (i : w64) (hs' : GoSlice) (hvs' : List walOp),
      "i" ∷ i_ptr ↦ i ∗ "h" ∷ h_ptr ↦ hs' ∗ "Hh" ∷ hs' ↦* hvs' ∗
      "Hhcap" ∷ ownSliceCap walOp hs' (DFrac.own 1) ∗
      "Hhel" ∷ opsElems hvs' (cd.h ++ o.since.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.since'.len⌝ : IProp GF) $$ [i h Hh Hhcap]
  · iexists W64 0, hs, hvs
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.take_zero, List.append_nil]
    iframe
    isplitl []
    · iexact Hhel
    ipureintro; constructor <;> word
  wp_for HI2
  icases Hhel with #Hhel
  by_cases hlt2 : sint.Z i < sint.Z v.since'.len
  · rw [if_pos (by simp [hlt2])]
    have hil : sint.nat i < svs.length := by
      have : sint.nat i < sint.nat v.since'.len := by word
      omega
    obtain ⟨sv, Hsvi⟩ : ∃ sv, svs[sint.nat i]? = some sv := ⟨_, List.getElem?_eq_getElem hil⟩
    have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z v.since'.len := ⟨Hi.1, hlt2⟩
    icases ownSlice_elem_acc (sint.Z i) sv v.since' DFrac.discard svs Hi.1
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
      have : sint.nat i = sint.nat v.since'.len := by word
      omega
    have hH : cd.h ++ List.take (sint.nat i) o.since = tCandHist o cd := by
      rw [hin2, List.take_length]; rfl
    rw [hH]
    wp_auto
    imod ownSlice_persist $$ Hh with #Hh
    wp_apply (wp_walFold hs' (tCandHist o cd)) as %fv ⟨%f, #Hf, %Hfe⟩
    · iunfold opsRep; iexists hvs'; isplitl []
      · iexact Hh
      · iexact Hhel
    iunfold contentsRep at Hf
    icases Hf with ⟨%Hff, #Hfe⟩
    have hentwf : ∀ x ∈ f.ents, tEntWf x := by
      intro x hx
      obtain ⟨op, hop, hsn, hxo⟩ := Hfe x hx
      have hcdm : cd ∈ o.cands := List.mem_of_getElem? Hcd
      exact (hwf.2 cd hcdm).1 op hop |>.2 hsn x hxo
    ihave %Hfel := ownSlice_len $$ Hfe
    try wp_auto
    wp_if_destruct
    · resend_nop
    wp_if_destruct
    · resend_nop
    wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %esl0 ⟨Hesl0, Hcap0⟩
    · ipureintro; word
    simp only [List.replicate_zero]
    wp_auto
    ihave HI : (∃ (i : w64) (esl : GoSlice) (es : List TEnt),
        "i" ∷ i_ptr ↦ i ∗ "es" ∷ es_ptr ↦ esl ∗ "Hes" ∷ esl ↦* es ∗
        "Hcap" ∷ ownSliceCap TEnt esl (DFrac.own 1) ∗
        "%Hi" ∷ ⌜uint.nat (l - fv.baseIdx') ≤ uint.nat i ∧ uint.nat i ≤ uint.nat (l - fv.baseIdx') + 3 ∧
          es.length = uint.nat i - uint.nat (l - fv.baseIdx') ∧ ∀ x ∈ es, x ∈ f.ents⌝ : IProp GF)
        $$ [i es Hesl0 Hcap0]
    · iexists _, esl0, []
      iframe
      ipureintro
      refine ⟨Nat.le_refl _, by omega, by simp, by simp⟩
    wp_for HI
    wp_if_destruct
    · try wp_auto
      by_cases h3 : uint.Z i < uint.Z (l - fv.baseIdx' + W64 3)
      · simp only [h3, _root_.decide_true, ↓reduceIte]
        try wp_auto
        have hil : uint.nat i < f.ents.length := by
          rw [Hfel.1]
          have : uint.Z i < uint.Z fv.ents'.len := by assumption
          word
        obtain ⟨x, Hx⟩ : ∃ x, f.ents[uint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
        have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z fv.ents'.len := by
          have : uint.Z i < uint.Z fv.ents'.len := by assumption
          constructor <;> word
        icases ownSlice_elem_acc (sint.Z i) x fv.ents' DFrac.discard f.ents hb.1
          (by
            have : (sint.Z i).toNat = uint.nat i := by word
            rw [this]; exact Hx) $$ Hfe with ⟨Hxv, -⟩
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_auto
        wp_if_destruct
        · wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %osl ⟨Hosl, -⟩
          wp_apply wp_slice_append $$ [$Hes $Hcap $Hosl] as %esl2 ⟨Hes2, Hcap2, -⟩
          wp_for_post
          iframe
          iexists i + W64 1, esl2, es ++ [x]
          iframe
          ipureintro
          obtain ⟨h1, h2, h3', h4⟩ := Hi
          have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
          refine ⟨by omega, by word, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
          intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · exact h4 y hy
          · simp only [List.mem_singleton] at hy
            subst hy
            exact List.mem_of_getElem? Hx
        · wp_for_post
          resend_rest
      · simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
        resend_rest
    · resend_rest

end proof

end etcd_wal
end EtcdGrove
end Perennial
