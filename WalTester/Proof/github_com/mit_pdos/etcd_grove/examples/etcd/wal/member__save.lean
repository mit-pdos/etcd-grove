/- Lean-first (no Rocq counterpart). The proof of `member.save`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__save
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.hsEmpty
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walMustSync
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.phsNext
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.toHS
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.toRaft
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SaveAu
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__syncLemmas

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

/-- The oracle with `lastHS` written. -/
theorem oracleRep_lastHS (v : oracle) (o : TOracle) (x : THs) :
    oracleRep (GF := GF) v o ⊢
      oracleRep (oracle.mk v.created' v.cands' v.since' v.synced' x v.opens') { o with lastHS := x } := by
  iintro Hr
  iunfold oracleRep at Hr
  icases Hr with ⟨%Hf, Hcs, #Hsince, Hscap, #Hop, Hopcap⟩
  iunfold oracleRep
  isplitr
  · ipureintro; exact ⟨Hf.1, Hf.2.1, rfl⟩
  iframe
  isplitl []
  · iexact Hsince
  · iexact Hop

set_option hygiene false in
/-- **`save`'s path after the empty check** (`hne`): the append and its store, the entries' loop,
`Save`, the sync's store, `lastHS`. Unhygienic: it names the proof's hypotheses. -/
macro "save_main" : tactic => `(tactic| (
  -- `m.o.since = append(m.o.since, walOp{hs: h, ents: es})`
  iunfold oracleRep at Hrep
  icases Hrep with ⟨%Hf, Hcs, #Hsince, Hscap, #Hop, Hopcap⟩
  iunfold opsRep at Hsince
  icases Hsince with ⟨%vs, #Hs, #Hel⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  wp_apply (wp_slice_append_persistent (V := walOp) v.since' vs _ _ (DFrac.own 1)) $$ [Hs Hscap Hosl]
    as %s1 ⟨#Hs1, Hscap, -⟩
  · iframe; iframe #
  try wp_auto
  ihave Hrep1 : oracleRep (oracle.mk v.created' v.cands' s1 v.synced' v.lastHS' v.opens')
      (tSaveO1 o h es) $$ [Hcs Hscap Hopcap]
  · iunfold oracleRep
    simp only [tSaveO1]
    isplitr
    · ipureintro; exact Hf
    iframe
    isplitl []
    · iunfold opsRep
      iexists _
      iframe Hs1
      iapply opsElems_snoc
      iframe Hel
      unfold opRep tSaveOp
      iframe Hes
      ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    · iexact Hop
  ihave #Hrel := tRelI_save1 W e.area o c d h es hok.1 hok.2.1 (tCandOk_save1 hok h es hes ht hsim)
    (tCheckWf_saveO1 hcwf h es hes ht hsm1)
    $$ [Hsl Hnm]
  · isplitl []
    · iexact Hsl
    · iexact Hnm
  iunfold tPerm at Hperm
  icases Hperm with ⟨Hpw_, Hperm⟩
  wp_apply (wp_store W e γ _ os (tSaveO1 o h es) (some d) 1 hf hsm1) $$ [Hh Hperm Hrep1 Ho Hwo]
    as ⟨Hh, Hperm, Hrep1, Ho, Hwo⟩
  · iframe; iframe #
  ihave Hperm : tPerm (GF := GF) e qc $$ [Hpw_ Hperm]
  · iunfold tPerm; iframe
  try wp_auto
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) esl.len (by word)) as %rs0 ⟨Hrs, Hrcap, -⟩
  ihave HI : (∃ (j : w64) (rs : GoSlice) (ls : List Loc),
      "i" ∷ i_ptr ↦ j ∗ "res" ∷ res_ptr ↦ rs ∗ "Hrs" ∷ rs ↦* ls ∗
      "Hrcap" ∷ ownSliceCap Loc rs (DFrac.own 1) ∗
      "Hents" ∷ walEntsIn (walRaftP (GF := GF)) ls ((es.take (sint.nat j)).map absEnt) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z esl.len⌝ : IProp GF) $$ [i res Hrs Hrcap]
  · iexists W64 0, rs0, []
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.replicate_zero, List.map_nil]
    iframe
    isplitr
    · unfold walEntsIn; iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
    ipureintro; constructor <;> word
  wp_for HI
  try wp_auto
  by_cases hjl0 : sint.Z j < sint.Z esl.len
  · first
      | rw [if_pos (by simp [hjl0])]
      | rw [if_pos (by simp only [decide_eq_true_eq]; exact hjl0)]
    try wp_auto
    have hjl : sint.nat j < es.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, es[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z esl.len := ⟨Hj.1, hjl0⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index esl (sint.Z j) es DFrac.discard x Hj.1 $$ [Hes] as -
    · iframe #; ipureintro; exact Hx
    have hxwf := hes x (List.mem_of_getElem? Hx)
    wp_apply (wp_toRaft x (by have := hxwf.1; omega) (by have := hxwf.2.1; omega)) as %l #Hl
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hrs Hrcap Hosl] as %rs' ⟨Hrs, Hrcap, -⟩
    · iframe
    wp_for_post
    iframe
    iexists j + W64 1, rs', ls ++ [l]
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    rw [hj1, List.take_add_one, Hx]
    simp only [Option.toList, List.map_append, List.map_cons, List.map_nil]
    iframe
    isplitl [Hents]
    · unfold walEntsIn
      iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
      iframe
      iapply (show walEntIn (GF := GF) l (absEnt x) ⊢ (walRaftP (GF := GF)).entIn l (absEnt x) from .rfl)
      iexact Hl
    ipureintro; constructor <;> word
  · first
      | rw [if_neg (by simp [hjl0]), if_neg (by simp [hjl0])]
      | rw [if_neg (by simp [hjl0]), if_pos (by simp [hjl0])]
      | rw [if_neg (by simp only [decide_eq_true_eq]; exact hjl0),
          if_neg (by simp only [decide_eq_true_eq]; exact hjl0)]
    have hjn : sint.nat j = es.length := by word
    rw [hjn, List.take_length]
    try wp_auto
    wp_apply wp_toHS as %hp #Hhp
    try wp_auto
    imod ownSlice_persist $$ Hrs with #Hrs
    obtain ⟨hidx, henc⟩ := tEnts_saveOk es hes
    by_cases hfit : saveBatchBytes walRaftMr (es.map absEnt) ≤ maxSaveBatch
    rotate_left
    · -- (fix 0009) a batch past `MaxSaveBatchBytes`: refused before anything is committed (`Save`'s update
      -- vacuous, its `Q` false), the member stops
      iapply fupd_wp
      imod walOpenWS_alloc (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) ⊤ 0 $$ [Hwf]
        with ⟨%γs, Hws, %hγ0⟩
      · iapply walHdl_of_wf (W := W) ioNone _ _ _ _ 0 walCov_ioNone $$ Hwf
      rcases γs with ⟨γs1, γs2, γsi⟩; dsimp only at hγ0; subst hγ0
      let γs : WalShN := ⟨γs1, γs2, 0⟩
      imodintro
      wp_apply (lc := 1) (wp_Save W e.R e.jr (e.area) w (tWalDir e.area) γs 1 hp (absHs h) rs ls
          (es.map absEnt) true (fun _ => iprop(False)) (fun hc => absurd hc walCov_ioNone)) $$ [Hws Hents]
        as %err Hr
      · iframe; iframe #
        isplitr
        · ipureintro; exact Or.inr rfl
        isplitl []
        · iapply (show walHsIn (GF := GF) hp (absHs h) ⊢ (walRaftP (GF := GF)).hsIn hp (absHs h) from .rfl)
          iexact Hhp
        isplitr
        · ipureintro; exact hidx
        isplitr
        · ipureintro; exact henc
        iintro %hle
        exact absurd hle hfit
      icases Hr with (⟨-, -, %d0, HF, -⟩ | ⟨-, %d0, HF⟩ | ⟨%Herr, -⟩)
      · icases HF with %hF; exact hF.elim
      · icases HF with %hF; exact hF.elim
      cases err with
      | nil => exact absurd rfl Herr.1
      | ok ie =>
      try wp_auto
      iapply HΦ
      iframe Hh Hperm Hpath Hw
      iexists _
      iframe Hov
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitl [Ho]
      · iexists _; iexact Ho
      ipureintro; trivial
    ihave Hau := tInv_saveAu W e γ o c d h es hok hes ht hsim $$ [Hwo Ho]
    · iframe; iframe #
    -- the member's handle, shared for the call (the tester assumes nothing of I/O errors: `ioNone`) and
    -- taken back after it
    iapply fupd_wp
    imod walOpenWS_alloc (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) ⊤ 0 $$ [Hwf]
      with ⟨%γs, Hws, %hγ0⟩
    · iapply walHdl_of_wf (W := W) ioNone _ _ _ _ 0 walCov_ioNone $$ Hwf
    rcases γs with ⟨γs1, γs2, γsi⟩; dsimp only at hγ0; subst hγ0
    let γs : WalShN := ⟨γs1, γs2, 0⟩
    imodintro
    wp_apply (lc := 1) (wp_Save W e.R e.jr (e.area) w (tWalDir e.area) γs 1 hp (absHs h) rs ls
        (es.map absEnt) true _ (fun hc => absurd hc walCov_ioNone)) $$ [Hws Hents Hau]
      as %err Hr
    · iframe Hws Hents; iframe #
      isplitr
      · ipureintro; exact Or.inr rfl
      isplitl []
      · iapply (show walHsIn (GF := GF) hp (absHs h) ⊢ (walRaftP (GF := GF)).hsIn hp (absHs h) from .rfl)
        iexact Hhp
      isplitr
      · ipureintro; exact hidx
      isplitr
      · ipureintro; exact henc
      iintro %_
      iexact Hau
    icases Hr with (⟨%Herr, Hws, %d0, ⟨%hd0, Hwo, Ho⟩, #Hlen1, Hsync⟩ | ⟨%Herr, %d0, ⟨%hd0, Hwo, Ho⟩⟩ |
      ⟨%Hbig, -⟩)
    rotate_left 2
    · exfalso; exact absurd hfit (Nat.not_le.mpr Hbig.2)
    · subst Herr
      iapply fupd_wp
      imod walOpenWS_reclaim (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) γs $$ [Hws Hlc1]
        with Hwf
      · iframe Hws Hlc1
      imodintro
      ihave Hwf := walHdl_wf (W := W) ioNone _ _ _ _ $$ Hwf
      subst d0
      try wp_auto
      wp_apply wp_mustSync
      have hms : tMustSync v.lastHS' h (sint.nat esl.len) = tMustSync o.lastHS h es.length := by
        rw [Hf.2.2, ← Hlen.1]
      rw [hms]
      have hd' := tMemOk_save1 hok h es hes ht hsim
      have hsv : tSaveO o h es = { (if tMustSync o.lastHS h es.length then tSynced (tSaveO1 o h es)
          else tSaveO1 o h es) with lastHS := tPhsNext o.lastHS h } := by
        unfold tSaveO; simp only [hne, Bool.false_eq_true, ↓reduceIte]
      cases hMS : tMustSync o.lastHS h es.length
      · -- no sync
        simp only [hMS, Bool.false_eq_true, ↓reduceIte] at hsv
        try wp_auto
        wp_apply wp_phsNext
        try wp_auto
        iapply HΦ
        rw [Hf.2.2, hsv]
        iframe Hh Hperm Hpath Hw
        iexists _
        iframe Hov
        isplitl [Ho]
        · iexists _; iexact Ho
        simp only [↓reduceIte]
        iexists tSaveD d h es
        iframe Hwo Hwf
        isplitl [Hrep1]
        · iapply (oracleRep_lastHS (oracle.mk v.created' v.cands' s1 v.synced' o.lastHS v.opens')
            (tSaveO1 o h es) (tPhsNext o.lastHS h))
          iexact Hrep1
        isplitr
        · ipureintro; exact ⟨hd', tMemHs_save hhs h es _⟩
        have hcm : tCandMark ({ tSaveO1 o h es with lastHS := tPhsNext o.lastHS h } : TOracle) c =
            tCandMark o c := rfl
        rw [hcm]
        isplitl []
        · iexact Hsl
        rw [show (tSaveD d h es).H.length = d.H.length + 1 by simp [tSaveD]]
        iexact Hlen1
      · -- the save synced: the mark moved and stored
        simp only [hMS, ↓reduceIte] at hsv
        try wp_auto
        ihave ⟨%hl, Hrep1⟩ := oracleRep_synced _ _ $$ Hrep1
        ihave #Hsy := Hsync $$ [] 
        · ipureintro; exact (tMustSync_iff hhs h es).1 hMS
        ihave #Hrel2 := tRelI_synced W e.area (tSaveO1 o h es) c (tSaveD d h es) hd' hl
          (tCheckWf_saveO1 hcwf h es hes ht hsm1) $$ [Hsy Hnm]
        · isplitl []
          · rw [show (tSaveD d h es).H.length = d.H.length + 1 by simp [tSaveD]]; iexact Hsy
          · iexact Hnm
        iunfold tPerm at Hperm
        icases Hperm with ⟨Hpw_, Hperm⟩
        wp_apply (wp_store W e γ _ (tSaveO1 o h es) (tSynced (tSaveO1 o h es)) (some (tSaveD d h es))
            1 hf hsm2) $$ [Hh Hperm Hrep1 Ho Hwo]
          as ⟨Hh, Hperm, Hrep1, Ho, Hwo⟩
        · iframe; iframe #
        ihave Hperm : tPerm (GF := GF) e qc $$ [Hpw_ Hperm]
        · iunfold tPerm; iframe
        try wp_auto
        wp_apply wp_phsNext
        try wp_auto
        iapply HΦ
        rw [Hf.2.2, hsv]
        iframe Hh Hperm Hpath Hw
        iexists _
        iframe Hov
        isplitl [Ho]
        · iexists _; iexact Ho
        simp only [↓reduceIte]
        iexists tSaveD d h es
        iframe Hwo Hwf
        isplitl [Hrep1]
        · iapply (oracleRep_lastHS (oracle.mk v.created' v.cands' s1 s1.len o.lastHS v.opens')
            (tSynced (tSaveO1 o h es)) (tPhsNext o.lastHS h))
          iexact Hrep1
        isplitr
        · ipureintro; exact ⟨tMemOk_synced (o := tSaveO1 o h es) hd' hl, tMemHs_save hhs h es _⟩
        have hcm2 : tCandMark ({ tSynced (tSaveO1 o h es) with lastHS := tPhsNext o.lastHS h } : TOracle) c =
            d.H.length + 1 := by
          show tCandMark (tSynced (tSaveO1 o h es)) c = _
          rw [tSynced_mark _ c hl, ← tMemOk_len hd']; simp [tSaveD]
        rw [hcm2]
        isplitl []
        · iexact Hsy
        rw [show (tSaveD d h es).H.length = d.H.length + 1 by simp [tSaveD]]
        iexact Hlen1
    · -- `Save` failed: the member stops
      cases err with
      | nil => exact absurd rfl Herr.1
      | ok ie =>
      try wp_auto
      iapply HΦ
      iframe Hh Hperm Hpath Hw
      iexists _
      iframe Hov
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitl [Ho]
      · iexists _; iexact Ho
      ipureintro; trivial))

theorem member.save.wp_proof
    (wp_hsEmpty : hsEmpty.spec (GF := GF) (hG := hG))
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_toRaft : toRaft.spec (GF := GF) (hG := hG))
    (wp_toHS : toHS.spec (GF := GF) (hG := hG))
    (wp_mustSync : walMustSync.spec (GF := GF) (hG := hG))
    (wp_phsNext : phsNext.spec (GF := GF) (hG := hG))
    (wp_Save : ∀ W : WalGS GF,
      go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.spec (W := W) (Sio := ioNone) (walRaftP (GF := GF))
        walRaftMr) :
    member.save.spec (GF := GF) (hG := hG) := by
  intro W e γ m w v o os c d qc h esl es hf hok hhs hes ht hsm1 hsm2 hsim hcwf
  wp_start as ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, Hpath, Hw, Hov, Hrep, Ho, Hwo, #Hes, #Harea, Hwf,
    #Hnm, #Hsl, #Hll⟩
  ihave %Hlen := ownSlice_len $$ Hes
  try wp_auto
  wp_apply wp_hsEmpty
  cases hE : tHsEmpty h
  · try wp_auto
    have hne : ¬ (tHsEmpty h && es.isEmpty) = true := by simp [hE]
    save_main
  · try wp_auto
    wp_if_destruct
    · -- the empty save: nothing done
      have hnil : es = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hlen.1]; word
      subst hnil
      try wp_auto
      iapply HΦ
      have hso : tSaveO o h [] = o := by unfold tSaveO; simp [hE]
      rw [hso]
      iframe Hh Hperm Hpath Hw
      iexists v
      iframe Hov
      isplitl [Ho]
      · iexists os; iexact Ho
      simp only [↓reduceIte]
      iexists d
      iframe
      iframe #
      ipureintro; exact ⟨hok, hhs⟩
    · have hne : ¬ (tHsEmpty h && es.isEmpty) = true := by
        intro hc
        rw [Bool.and_eq_true] at hc
        have h0 := List.isEmpty_iff.1 hc.2
        apply Hif; subst h0; simp at Hlen; word
      try wp_auto
      save_main

end proof

end etcd_wal
end EtcdGrove
end Perennial
