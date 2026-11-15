/- Lean-first (no Rocq counterpart). The proof of `member.opCommit`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opCommit
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__hs
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__save

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

theorem member.opCommit.wp_proof (wp_choose : rnd.choose.spec (GF := GF) (hG := hG))
    (wp_hs : member.hs.spec (GF := GF) (hG := hG)) (wp_save : member.save.spec (GF := GF) (hG := hG)) :
    member.opCommit.spec (GF := GF) (hG := hG) := by
  intro W e γ m w v o os c d qc t vo cm l bs r rv hf hok hhs ht hms hsm hcwf
  wp_start as ⟨Hres, Ht, Hv, Hc, Hl, Hr, Hrv⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe
    ileft
    iframe
    ipureintro; exact ⟨rfl, by word⟩
  wp_apply wp_choose $$ [$Hrv] as %k ⟨⟨%rv', Hrv⟩, %hk⟩
  have hk' : uint.nat k < uint.nat (l - cm) := by
    rw [if_neg (by intro h; apply Hif; word)] at hk; exact hk
  wp_apply (wp_hs m t vo (cm + W64 1 + k)) $$ [$Ht $Hv $Hc] as ⟨Ht, Hv, Hc⟩
  wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %esl ⟨Hesl, -⟩
  · ipureintro; word
  simp only [List.replicate_zero]
  imod ownSlice_persist $$ Hesl with #Hesl
  wp_auto
  iunfold memSaveRes at Hres
  icases Hres with ⟨#H1, #H2, #H3, #H4, H5, H6, H7, H8, H9, H10, H11, H12, #H13, H14, #H15, #H16, #H17⟩
  have hstep := tMemSim_save (h := hardState.mk t vo (cm + W64 1 + k)) (es := []) (lo := 0) hms
    (by simp only; word) (Or.inl rfl) l (by simp) (by simp only; word)
  wp_apply (wp_save W e γ m w v o os c d qc (hardState.mk t vo (cm + W64 1 + k)) esl [] hf hok hhs
    (by simp) ht (hsm _).1 (hsm _).2 hstep.1 hcwf) $$ [H5 H6 H7 H8 H9 H10 H11 H12 H14] as %b Hpost
  · iframe
    iframe Hesl H13 H15 H16 H17 H1 H2 H3 H4
  iapply HΦ
  iframe
  iright
  iexists (cm + W64 1 + k)
  iframe
  isplitr
  · ipureintro; exact ⟨by word, by word, hstep.2⟩
  unfold memSavePost
  iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
