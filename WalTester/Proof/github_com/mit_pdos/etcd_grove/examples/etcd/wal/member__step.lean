/- Lean-first (no Rocq counterpart). The proof of `member.step`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__step
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.fits
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opEntries
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opResend
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opCommit
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opTerm
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opOwnSnap
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opRecvSnap
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__sync
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__close
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.StepLive

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

set_option maxHeartbeats 4000000 in
theorem member.step.wp_proof (wp_fits : fits.spec (GF := GF) (hG := hG))
    (wp_choose : rnd.choose.spec (GF := GF) (hG := hG))
    (wp_opEntries : member.opEntries.spec (GF := GF) (hG := hG))
    (wp_opResend : member.opResend.spec (GF := GF) (hG := hG))
    (wp_opCommit : member.opCommit.spec (GF := GF) (hG := hG))
    (wp_opTerm : member.opTerm.spec (GF := GF) (hG := hG))
    (wp_opOwnSnap : member.opOwnSnap.spec (GF := GF) (hG := hG))
    (wp_opRecvSnap : member.opRecvSnap.spec (GF := GF) (hG := hG))
    (wp_sync : member.sync.spec (GF := GF) (hG := hG))
    (wp_close : member.close.spec (GF := GF) (hG := hG))
    (wp_restart : member.restart.spec (GF := GF) (hG := hG)) :
    member.step.spec (GF := GF) (hG := hG) := by
  intro W e γ m lg o qp hmn hf hpath hpf
  wp_start as ⟨Hlive, #Hzap, Hlg, Hwd, Hpth, Hares⟩
  iunfold memLive at Hlive
  icases Hlive with ⟨%w, %v, %os, %c, %d, %t, %vo, %cm, %bs, %l, %tm, %M, %r, %rv, Hres, Ht, Hv, Hc, Hb,
    Hl, Htm, HM, Hr, Hrv, Hpw, %Hfacts⟩
  obtain ⟨hok, hhs, hfl, hwf, hms⟩ := Hfacts
  ihave ⟨Hres, #Hpers⟩ := memSaveRes_pers W e γ m w v o os c d _ $$ Hres
  iunfold memSaveRes at Hres
  icases Hres with ⟨#H1, #H2, #H3, #H4, H5, H6, H7, H8, H9, Hrep, H11, H12, #H13, H14, #H15, #H16, #H17⟩
  wp_auto
  wp_apply (wp_fits v o (W64 256) (by word)) $$ [$Hrep] as %bf ⟨Hrep, %hbf⟩
  cases bf
  · wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  have hroom : tOrRoom o 256 := by have := hbf.1 rfl; simpa using this
  have hsm : tOrSmall o := tOrSmall_of_room (tOrRoom_mono hroom (by omega))
  have hl0 := tOrSmall_since_lt hsm
  wp_auto
  wp_apply wp_choose $$ [$Hrv] as %k ⟨⟨%rv1, Hrv⟩, %hk⟩
  rw [if_neg (by decide)] at hk
  try wp_auto
  wp_if_destruct
  · ihave Hres : memSaveRes W e γ m w v o os c d (1 : Qp).half $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
    · iunfold memSaveRes; iframe; iframe #
    wp_apply (wp_opEntries W e γ m w v o os c d _ t vo cm bs l tm M r rv1 hf hok hhs hfl.1
        (tOrRoom_mono hroom (by omega)) hms hwf) $$ [$Hres $Ht $Hv $Hc $Hb $Hl $Htm $HM $Hr $Hrv] as %b Hpost
    icases Hpost with ⟨Ht, Hv, Hb, Htm, Hr, ⟨%rv2, Hrv⟩, Hpost⟩
    try wp_auto
    iapply HΦ
    iframe Hpth Hares Hlg Hwd
    icases Hpost with (⟨%hb, Hc, Hl, HM, Hres⟩ | ⟨%cm', %l', %es, %M', %hfx, Hc, Hl, HM, Hpost⟩)
    · obtain ⟨rfl, -⟩ := hb
      simp only [↓reduceIte]
      iexists o
      isplitl
      · iapply memLive_intro W e γ m w v o os c d _ t vo cm bs l tm M r rv2 hok hhs hfl hwf hms
        iframe; iunfold memFields; iframe
      · ipureintro; exact hsm
    · cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial
      · simp only [↓reduceIte]
        obtain ⟨h1, h2, h3, h4, h5⟩ := hfx
        iexists _
        isplitl
        · iapply memLive_post W e γ m w o c _ (hardState.mk t vo cm') es t vo cm' bs l' tm M' r rv2
            ⟨hfl.1, tTermsFrom_ok h4 hfl⟩ (tCheckWf_step hwf hroom _ h2 (fun x hx => (h3 x hx).1) hfl.1) h5
          iframe; iframe #; iunfold memFields; iframe
        · ipureintro; exact tOrSmall_saveO_room hroom _ h2
  try wp_auto
  wp_if_destruct
  · -- opResend
    ihave Hres : memSaveRes W e γ m w v o os c d (1 : Qp).half $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
    · iunfold memSaveRes; iframe; iframe #
    wp_apply (wp_opResend W e γ m w v o os c d _ t vo cm l bs tm M hf hok hhs hwf hfl
        (tOrRoom_mono hroom (by omega)) hms) $$ [$Hres $Ht $Hv $Hc $Hl $Htm $HM] as %b Hpost
    icases Hpost with ⟨Hv, Hc, Htm, Hpost⟩
    try wp_auto
    iapply HΦ
    iframe Hpth Hares Hlg Hwd
    icases Hpost with (⟨%hb, Ht, Hl, HM, Hres⟩ | ⟨%t', %l', %es, %M', %hfx, Ht, Hl, HM, Hpost⟩)
    · subst hb
      simp only [↓reduceIte]
      iexists o
      isplitl
      · iapply memLive_intro W e γ m w v o os c d _ t vo cm bs l tm M r rv1 hok hhs hfl hwf hms
        iframe; iunfold memFields; iframe
      · ipureintro; exact hsm
    · cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial
      · simp only [↓reduceIte]
        obtain ⟨h1, h2, h3, h4, h5⟩ := hfx
        iexists _
        isplitl
        · iapply memLive_post W e γ m w o c _ (hardState.mk t' vo cm) es t' vo cm bs l' tm M' r rv1
            (h4 hfl) (tCheckWf_step hwf hroom _ (by omega) h3 (h4 hfl).1) h5
          iframe; iframe #; iunfold memFields; iframe
        · ipureintro; exact tOrSmall_saveO_room hroom _ (by omega)
  try wp_auto
  wp_if_destruct
  · -- opCommit
    ihave Hres : memSaveRes W e γ m w v o os c d (1 : Qp).half $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
    · iunfold memSaveRes; iframe; iframe #
    wp_apply (wp_opCommit W e γ m w v o os c d _ t vo cm l bs r rv1 hf hok hhs hfl.1 hms
        (tOrRoom_saveNil (tOrRoom_mono hroom (by omega))) hwf) $$ [$Hres $Ht $Hv $Hc $Hl $Hr $Hrv] as %b Hpost
    icases Hpost with ⟨Ht, Hv, Hl, Hr, ⟨%rv2, Hrv⟩, Hpost⟩
    try wp_auto
    iapply HΦ
    iframe Hpth Hares Hlg Hwd
    icases Hpost with (⟨%hb, Hc, Hres⟩ | ⟨%cm', %hfx, Hc, Hpost⟩)
    · obtain ⟨rfl, -⟩ := hb
      simp only [↓reduceIte]
      iexists o
      isplitl
      · iapply memLive_intro W e γ m w v o os c d _ t vo cm bs l tm M r rv2 hok hhs hfl hwf hms
        iframe; iunfold memFields; iframe
      · ipureintro; exact hsm
    · cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial
      · simp only [↓reduceIte]
        iexists _
        isplitl
        · iapply memLive_post W e γ m w o c _ (hardState.mk t vo cm') [] t vo cm' bs l tm M r rv2
            hfl (tCheckWf_step hwf hroom _ (by simp) (by simp) hfl.1) hfx.2.2
          iframe; iframe #; iunfold memFields; iframe
        · ipureintro; exact tOrSmall_saveO_room hroom _ (by simp)
  try wp_auto
  wp_if_destruct
  · -- opTerm
    ihave Hres : memSaveRes W e γ m w v o os c d (1 : Qp).half $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
    · iunfold memSaveRes; iframe; iframe #
    wp_apply (wp_opTerm W e γ m w v o os c d _ t vo cm bs l r rv1 hf hok hhs hfl.1 hms
        (tOrRoom_saveNil (tOrRoom_mono hroom (by omega))) hwf) $$ [$Hres $Ht $Hv $Hc $Hr $Hrv] as %b Hpost
    icases Hpost with ⟨%vo', Ht, Hv, Hc, Hr, ⟨%rv2, Hrv⟩, Hpost, %hfx⟩
    try wp_auto
    iapply HΦ
    iframe Hpth Hares Hlg Hwd
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial
    · simp only [↓reduceIte]
      iexists _
      isplitl
      · iapply memLive_post W e γ m w o c _ (hardState.mk (tNextTerm t) vo' cm) [] (tNextTerm t) vo' cm bs l
          tm M r rv2 ⟨tNextTerm_lt hfl.1, hfl.2⟩ (tCheckWf_step hwf hroom _ (by simp) (by simp)
            (tNextTerm_lt hfl.1)) hfx
        iframe; iframe #; iunfold memFields; iframe
      · ipureintro; exact tOrSmall_saveO_room hroom _ (by simp)
  try wp_auto
  wp_if_destruct
  · -- opOwnSnap
    ihave Hres : memSaveRes W e γ m w v o os c d (1 : Qp).half $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
    · iunfold memSaveRes; iframe; iframe #
    ihave Hlive := memLive_intro W e γ m w v o os c d _ t vo cm bs l tm M r rv1 hok hhs hfl hwf hms
      $$ [Hres Ht Hv Hc Hb Hl Htm HM Hr Hrv Hpw]
    · iframe; iunfold memFields; iframe
    wp_apply (wp_opOwnSnap W e γ m lg _ o hf (tOrRoom_mono hroom (by omega))) $$ [$Hlive $Hlg $Hwd]
      as %b ⟨Hlg, Hwd, Hpost⟩
    try wp_auto
    iapply HΦ
    iframe Hpth Hares Hlg Hwd
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial
    · simp only [↓reduceIte]
      icases Hpost with ⟨%o', Hlive, %hlen⟩
      iexists o'; iframe Hlive; ipureintro; exact tOrSmall_grow hroom hlen (by omega)
  try wp_auto
  wp_if_destruct
  · -- opRecvSnap
    ihave Hres : memSaveRes W e γ m w v o os c d (1 : Qp).half $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
    · iunfold memSaveRes; iframe; iframe #
    ihave Hlive := memLive_intro W e γ m w v o os c d _ t vo cm bs l tm M r rv1 hok hhs hfl hwf hms
      $$ [Hres Ht Hv Hc Hb Hl Htm HM Hr Hrv Hpw]
    · iframe; iunfold memFields; iframe
    wp_apply (wp_opRecvSnap W e γ m _ o hf (tOrRoom_mono hroom (by omega))) $$ [$Hlive] as %b Hpost
    try wp_auto
    iapply HΦ
    iframe Hpth Hares Hlg Hwd
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial
    · simp only [↓reduceIte]
      icases Hpost with ⟨%o', Hlive, %hlen⟩
      iexists o'; iframe Hlive; ipureintro; exact tOrSmall_grow hroom hlen (by omega)
  have hsyn : tOrSmall (tSynced o) := by unfold tOrSmall; rw [tEncodeOracle_synced]; exact hsm
  have hl : o.since.length < 2 ^ 64 := by omega
  try wp_auto
  wp_if_destruct
  · -- sync
    wp_apply (wp_sync W e γ m w v o os c d _ hf hok hsyn hwf) $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
      as %b Hpost
    · iframe; iframe #
    icases Hpost with ⟨H5, H6, H7, H8, %v', H9, H12, Hpost⟩
    try wp_auto
    iapply HΦ
    iframe Hpth Hares Hlg Hwd
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial
    · simp only [↓reduceIte]
      icases Hpost with ⟨Hrep, H11, H14, #Hll, #Hsl⟩
      iexists tSynced o
      isplitl
      · iapply memLive_intro W e γ m w v' (tSynced o) (tSynced o) c d _ t vo cm bs l tm M r rv1
          (tMemOk_synced hok hl) hhs hfl (tCheckWf_synced hwf hl) (tMemSim_congr (tSynced_hist o c) hms)
        iframe
        isplitl [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
        · iunfold memSaveRes; iframe; iframe H1 H2 H3 H4 H13 H15 Hll
          rw [tSynced_mark o c hl, ← tMemOk_len hok]; iexact Hsl
        iunfold memFields; iframe
      · ipureintro; exact hsyn
  try wp_auto
  wp_if_destruct
  · -- close, then restart
    wp_apply (wp_close W e γ m w v o os c d _ hf hok hsyn hwf) $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14 Hpw]
      as %b Hpost
    · iframe; iframe #
    icases Hpost with ⟨H5, H6, H7, H8, %v', H9, Hpost⟩
    cases b
    · try wp_auto
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
    simp only [↓reduceIte]
    icases Hpost with ⟨Hrep, H11, H12, Htok, H6b, #Hsl⟩
    try wp_auto
    ihave Hperm := tPerm_join e $$ [$H6 $H6b]
    ihave #HrW : tRelW (W := W) e.area (tSynced o) c $$ []
    · iunfold tRelW
      simp only [show (tSynced o).created = true from hok.1, ↓reduceIte]
      rw [tSynced_mark o c hl, ← tMemOk_len hok]
      isplitr
      · ipureintro; exact tCheckWf_synced hwf hl
      iframe #
    wp_apply (wp_restart W e γ m lg null v' (tSynced o) c (some d) qp t vo cm bs l tm r rv1 hmn hf hpath hpf
        hok.2.1 (fun d' hd' => by cases hd'; exact tMemOk_candOk hok hl) (tCheckWf_synced hwf hl))
      $$ [H5 Hperm Hpth Hares Htok Hlg Hwd H7 H8 H9 Ht Hv Hc Hb Hl Htm Hr Hrv Hrep H11 H12]
      as %ok Hpost
    · iframe; iframe H1 H2 H3 H4 H13 Hzap HrW
    icases Hpost with ⟨Hpth, Hares, Hlg, Hwd, Hpost⟩
    try wp_auto
    iapply HΦ
    iframe Hpth Hares Hlg Hwd
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial
    · simp only [↓reduceIte]
      icases Hpost with ⟨%o'', %ho'', Hlive⟩
      iexists o''; iframe Hlive; ipureintro; exact ho''.2
  -- nothing
  try wp_auto
  iapply HΦ
  iframe Hpth Hares Hlg Hwd
  simp only [↓reduceIte]
  iexists o
  ihave Hres : memSaveRes W e γ m w v o os c d (1 : Qp).half $$ [H5 H6 H7 H8 H9 Hrep H11 H12 H14]
  · iunfold memSaveRes; iframe; iframe #
  isplitl
  · iapply memLive_intro W e γ m w v o os c d _ t vo cm bs l tm M r rv1 hok hhs hfl hwf hms
    iframe; iunfold memFields; iframe
  · ipureintro; exact hsm

end proof

end etcd_wal
end EtcdGrove
end Perennial
