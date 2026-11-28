/-
(hraft_robust R3) The proof of `disk.(*Snaps).List` (`snap.go`), as `examples/snapstore`'s.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__List
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.List.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.List.spec (GF := GF) (hG := hG) :=
  fun g s Qc Wf Φ => by
  iintro ⟨#Hsn, HAU⟩
  ihave #Hsn2 := Hsn
  iunfold isSnaps at Hsn2
  icases Hsn2 with ⟨%mu, #Hpkg, #Hmu, #Hisl, #Hfile, #Hinv, #Hdinv, #Hos, #Hsh, %Hf⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (lc := 2) wp_Lock $$ [$Hisl] as ⟨Hlocked, HR⟩
  iunfold snapsLockInv at HR
  icases HR with ⟨%lat, %lt, %nid, %has, %mv, %dt, %qc, Hmem, %Hmv, #Hr, Hrec, Hdh, Hcp⟩
  icases snapMem_view s nid lt has mv dt lat Hmv $$ [$Hmem $Hr] with ⟨Hmem, #Hcell⟩
  icases snapsMemAt_open s nid lt has mv dt $$ Hmem with ⟨Hhas, Hmeta, Hdata, Hnid, Hm⟩
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod (snapRead g Qc Wf lat lt _) $$ Hinv Hrec Hlc1 Hlc2 HAU Hnc with ⟨Hnc, Hrec, HΦ⟩
  imodintro
  iframe Hnc
  wp_auto
  cases lat with
  | none =>
    simp only [latCell]
    icases Hcell with %Hhas
    subst Hhas
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral
      (go.GoType.SliceType (go.GoType.PointerType SnapshotMeta.ty))))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType SnapshotMeta.ty) []
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hhas Hmeta Hdata Hnid Hm Hrec Hdh Hcp]
    · inext; iunfold snapsLockInv; iexists _, lt, nid, _, mv, dt, qc
      iframe Hrec Hdh Hcp; iframe #; isplitl [Hhas Hmeta Hdata Hnid Hm]
      · iapply snapsMemAt_close; iframe
      ipureintro; exact Hmv
    iapply HΦ $$ Hsl
    ipureintro; rfl
  | some p =>
    obtain ⟨m, b⟩ := p
    simp only [latCell]
    icases Hcell with ⟨%Hhm, #Hb⟩
    obtain ⟨Hhas, Hmt⟩ := Hhm
    subst Hhas Hmt
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral
      (go.GoType.SliceType (go.GoType.PointerType SnapshotMeta.ty))))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType SnapshotMeta.ty) [m_ptr]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hhas Hmeta Hdata Hnid Hm Hrec Hdh Hcp]
    · inext; iunfold snapsLockInv; iexists _, lt, nid, _, mv, dt, qc
      iframe Hrec Hdh Hcp; iframe #; isplitl [Hhas Hmeta Hdata Hnid Hm]
      · iapply snapsMemAt_close; iframe
      ipureintro; exact Hmv
    iapply HΦ $$ Hsl
    iexists m_ptr
    iframe
    ipureintro; rfl

end proof

end Perennial
