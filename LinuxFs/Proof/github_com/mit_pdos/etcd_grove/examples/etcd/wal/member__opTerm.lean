/- Lean-first (no Rocq counterpart). The proof of `member.opTerm`. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opTerm
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__hs
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__save

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

theorem member.opTerm.wp_proof (wp_choose : rnd.choose.spec (GF := GF) (hG := hG))
    (wp_hs : member.hs.spec (GF := GF) (hG := hG)) (wp_save : member.save.spec (GF := GF) (hG := hG)) :
    member.opTerm.spec (GF := GF) (hG := hG) := by
  intro W e γ m w v o os c d qc t vo cm r rv hf hok hhs hsm
  wp_start as ⟨Hres, Ht, Hv, Hc, Hr, Hrv⟩
  wp_auto
  wp_if_destruct
  all_goals
    ihave Ht : m.[member, go!"term"] ↦ tNextTerm t $$ [Ht]
    · unfold tNextTerm
      by_cases ht : uint.nat t < 2 ^ 62
      · rw [if_pos ht]
        first | (exfalso; have := Hif; word) | iexact Ht
      · rw [if_neg ht]
        first | (exfalso; have := Hif; word) | iexact Ht
    wp_apply wp_choose $$ [$Hrv] as %k ⟨⟨%rv', Hrv⟩, -⟩
    wp_apply (wp_hs m (tNextTerm t) k cm) $$ [$Ht $Hv $Hc] as ⟨Ht, Hv, Hc⟩
    wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %esl ⟨Hesl, -⟩
    · ipureintro; word
    simp only [List.replicate_zero]
    imod ownSlice_persist $$ Hesl with #Hesl
    wp_auto
    iunfold memSaveRes at Hres
    icases Hres with ⟨#H1, #H2, #H3, #H4, H5, H6, H7, H8, H9, H10, H11, H12, #H13, H14, #H15, #H16⟩
    wp_apply (wp_save W e γ m w v o os c d qc (hardState.mk (tNextTerm t) k cm) esl [] hf hok hhs
      (by simp) (hsm _).1 (hsm _).2) $$ [H5 H6 H7 H8 H9 H10 H11 H12 H14] as %b Hpost
    · iframe
      iframe Hesl H13 H15 H16 H1 H2 H3 H4
    iapply HΦ
    iexists k
    iframe
    unfold memSavePost
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
