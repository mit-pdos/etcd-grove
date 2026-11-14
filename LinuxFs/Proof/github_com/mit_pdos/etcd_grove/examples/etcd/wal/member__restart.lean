/-
`member.restart.wp_proof` (W4c U5): `restartRead`, then on `readOK` `checkRestart` (its premise: the image
`restartRead` names is among the next candidates, `tRestart_ok`), `storeOracle` of the new oracle (its
relation: that candidate accounts for the WAL, `tRestart_ok`, with `ReadAll`'s `walSyncedLb` at the whole
history), `m.w = w` and `resume`. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__restart
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.checkRestart
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__resume

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

theorem member.restart.wp_proof
    (wp_read : restartRead.spec (GF := GF) (hG := hG))
    (wp_check : checkRestart.spec (GF := GF) (hG := hG))
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_resume : member.resume.spec (GF := GF) (hG := hG)) :
    member.restart.spec (GF := GF) (hG := hG) := by
  intro W e γ m lg w0 v o cd d qp t vo cm b l tm hf hpath hcr hcd hok hwf hrb hsm hsm2
  wp_start as ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, #Hzap, #Harea, Hpath, Hres, Htok, Hlg, Hwd, Hop, Hw,
    Hov, Ht, Hv, Hc, Hb, Hl, Htm, Hrep, Ho, Hwo, #Hsl, #Hnm⟩
  wp_auto
  wp_apply (wp_read W e γ lg m v o cd d qp hf hpath hcr hcd hok (hwf.2 cd hcd).2.trans (by norm_num)
      hrb hsm) $$ [Hh Hperm Hpath Hres Htok Hop Hov Hrep Ho Hwo]
    as %st %vc %w ⟨Hh, Hpath, Hres, Hop, %v1, %ls, %d1, Hov, Hrep, Ho, Hwo, %hd1, Hst⟩
  · iframe; iframe #
  obtain ⟨hls, hH, hcut, hok1⟩ := hd1
  wp_auto
  by_cases hst : st = W64 0
  · subst hst
    simp only [↓reduceIte]
    icases Hst with ⟨Hp1, %c, #Hc, %himg, Hwf, Hpw, #Hlen, #Hsl1, #Hnm1⟩
    obtain ⟨img, himgm, hI, hr⟩ := himg
    have hI1 : d1.H.map WalOpG.toM = img.map absOp := by rw [hH]; exact hI
    obtain ⟨c', hc', hh', hmem, hmhs, hmark, hcok⟩ :=
      tRestart_ok (o := tWithOpens o ls) hcd hok1 himgm hI1 hr
    wp_if_destruct
    wp_apply (wp_check v1 vc (tWithOpens o ls) c (tCheckWf_withOpens ls hwf)
        (by intro hn; rw [hn] at hc'; cases hc')) $$ [Hrep Hc] as %v2 ⟨Hrep, Hrep2⟩
    · iframe; iframe #
    wp_auto
    ihave #Hrel : tRelI (W := W) e.root (tCheckRestart (tWithOpens o ls) c) (some d1) $$ [Hsl1 Hnm1]
    · iunfold tRelI
      simp only [tCheckRestart, ↓reduceIte]
      iexists d1, c'
      isplitr
      · ipureintro; exact ⟨rfl, hc', hcok⟩
      isplitl
      · simp only [tCheckRestart] at hmark
        rw [hmark, hH]; iexact Hsl1
      · iexact Hnm1
    wp_apply (wp_store W e γ v2 (tWithOpens o ls) (tCheckRestart (tWithOpens o ls) c) (some d1)
        (1 : Qp).half hf (hsm2 ls c)) $$ [Hh Hp1 Hrep2 Ho Hwo]
      as ⟨Hh, Hp1, Hrep2, Ho, Hwo⟩
    · iframe; iframe #
    wp_auto
    wp_apply (wp_resume m vc c t vo cm b l tm) $$ [Ht Hv Hc Hb Hl Htm] as ⟨Ht, Hv, Hc, Hb, Hl, Htm⟩
    · iframe; iframe #
    wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    iexists w, c, tCheckRestart (tWithOpens o ls) c, c', d1
    iframe
    isplitr
    · ipureintro; exact ⟨⟨ls, rfl⟩, hmem, hmhs, by rw [hh']; exact hr⟩
    rw [hH, hmark]
    iframe #
  · wp_if_destruct
    · exact absurd rfl hst
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
