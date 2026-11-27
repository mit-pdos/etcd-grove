/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/fsmRestoreAndMeasure.lean (241f27e).
-/
/-
The proof of `raft.fsmRestoreAndMeasure` (stage 3, snap).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.fsmRestoreAndMeasure
public import Dsverify.Spec.github_com.hashicorp.raft.newCountingReadCloser
public import Dsverify.Spec.github_com.hashicorp.raft.countingReadCloser__Close
public import Dsverify.Spec.github_com.hashicorp.raft.countingReader__Read
public import Dsverify.Spec.github_com.hashicorp.raft.startSnapshotRestoreMonitor
public import Dsverify.Spec.github_com.hashicorp.raft.snapshotRestoreMonitor__StopAndWait

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

/-- The counting wrapper of a reader that never fails is one too (`Read` through the embedded
`*countingReader`, `Close` through the value). -/
theorem readCloserOk_counting
    (wp_cr_Read : github_com.hashicorp.raft.countingReader.Read.spec (GF := GF) (hG := hG))
    (wp_crc_Close : github_com.hashicorp.raft.countingReadCloser.Close.spec (GF := GF) (hG := hG))
    (crc cr : Loc) (rd : GoInterfaceOk) (R : List w8 → IProp GF) (eof : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
      crc ↦□ countingReadCloser.mk cr (GoInterface.ok rd) ∗ countingReaderIs cr (GoInterface.ok rd) ∗
      readCloserOk rd R eof ⊢
    readCloserOk ⟨go.GoType.PointerType countingReadCloser.ty, #crc⟩ R eof := by
  iintro ⟨#Hpkg, #Hcrc, #Hcr, #Hrc⟩
  ihave #Hrc' := Hrc
  unfold readCloserOk
  icases Hrc' with ⟨#HRd, -⟩
  isplit
  · unfold streamReaderOk
    iintro !> %p %buf %cs %Φ %Hbuf HR Hp HΦ
    dsimp only
    rw [MethodUnfold.method_unfold (t := go.GoType.PointerType countingReadCloser.ty) (m := go!"Read")]
    iStructNamed Hcrc
    wp_auto
    wp_apply wp_cr_Read cr rd R eof p buf cs $$ [$Hcr $HR $Hp] as %n %err ⟨%Hn, Hp, HR⟩
    · isplitl
      · unfold streamReaderOk; iexact HRd
      ipureintro; exact Hbuf
    iapply HΦ $$ %n %err [] Hp HR
    ipureintro; exact Hn
  · iintro !> %Φ HΦ
    dsimp only
    have h := MethodUnfold.method_unfold (t := go.GoType.PointerType countingReadCloser.ty)
      (m := go!"Close") #crc
    rw [h]
    wp_auto
    wp_apply wp_crc_Close cr rd R eof $$ []
    · unfold readCloserOk; iexact Hrc
    iexact HΦ

theorem github_com.hashicorp.raft.fsmRestoreAndMeasure.wp_proof
    (wp_newCountingReadCloser :
      github_com.hashicorp.raft.newCountingReadCloser.spec (GF := GF) (hG := hG))
    (wp_cr_Read : github_com.hashicorp.raft.countingReader.Read.spec (GF := GF) (hG := hG))
    (wp_crc_Close : github_com.hashicorp.raft.countingReadCloser.Close.spec (GF := GF) (hG := hG))
    (wp_startMonitor :
      github_com.hashicorp.raft.startSnapshotRestoreMonitor.spec (GF := GF) (hG := hG))
    (wp_StopAndWait :
      github_com.hashicorp.raft.snapshotRestoreMonitor.StopAndWait.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.fsmRestoreAndMeasure.spec (GF := GF) (hG := hG) := by
  intro fx γ i fsmOwn respP snapP k0 s rd R b eof size
  wp_start as ⟨#HisFSM, Hown, %Hk0, #Heof, #Hrc, HR, HsP⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_newCountingReadCloser as %crc ⟨%cr, #Hcrc, #Hcr⟩
  wp_apply wp_startMonitor as %mon #Hmon
  ihave #Hrcc := readCloserOk_counting wp_cr_Read wp_crc_Close crc cr rd R eof $$ [$Hpkg $Hcrc $Hcr $Hrc]
  ihave #HF := HisFSM
  unfold isFSM
  icases HF with ⟨-, -, -, -, #HRestore, -⟩
  wp_bind
  have hrdv : interface.mkOk (go.GoType.PointerType countingReadCloser.ty) #crc =
      GoInterface.ok ⟨go.GoType.PointerType countingReadCloser.ty, #crc⟩ := rfl
  rw [hrdv]
  iapply HRestore $$ %k0 %s %(⟨go.GoType.PointerType countingReadCloser.ty, #crc⟩ : GoInterfaceOk)
    %R %b %eof %_ Hown [] Heof Hrcc HR HsP
  · ipureintro; exact Hk0
  iintro %k0' %r Hown %Hk0' #Hnc Hr
  wp_auto
  wp_apply wp_StopAndWait mon $$ [$Hmon]
  iapply HΦ
  iexists k0', r
  iframe
  iframe #
  ipureintro; exact Hk0'

end proof

end Perennial
