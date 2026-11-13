/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/closeAll.lean`: the range loop
closes each `wal.rcFile` (`os.File.Close`, through the embedded field for a `*LockedFile`), logging
and collecting the messages of the errors (`Error()` of a `fmtErrorOk` error); then `nil`, or
`errors.New` of `strings.Join` of the messages.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.closeAll
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Spec.go_uber_org.zap.Error
public import LinuxFs.Spec.go_uber_org.zap.Logger__Warn
public import Perennial.Spec.strings.Join
public import Perennial.Spec.errors.New

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- A `wal.rcFile` is a non-nil interface. -/
theorem wal.rcFile_ok (rc : GoInterface) :
    wal.rcFile (GF := GF) rc ⊢ ∃ ii : GoInterfaceOk, ⌜rc = GoInterface.ok ii⌝ ∗ wal.rcFile rc := by
  iintro H
  iunfold wal.rcFile at H
  icases H with ⟨%f, %fd, %name, %d, Hty, Hf, Hfd⟩
  icases Hty with (%hty | ⟨%lf, %hty, #Hlf⟩)
  · subst hty
    iexists _
    isplitr
    · ipureintro; rfl
    iunfold wal.rcFile
    iexists f, fd, name, d
    iframe
    ileft
    ipureintro; rfl
  · subst hty
    iexists _
    isplitr
    · ipureintro; rfl
    iunfold wal.rcFile
    iexists f, fd, name, d
    iframe
    iright
    iexists lf
    iframe Hlf
    ipureintro; rfl

/-- `Close` of a `wal.rcFile`, through the interface's method. -/
theorem wal.wp_rcClose (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) (ii : GoInterfaceOk) :
    {{ osInv (GF := GF) ∗ wal.rcFile (GoInterface.ok ii) }}
      (App (Val #(methods ii.ty go!"Close" ii.v)) (Val #()))
    {{ (err : GoInterface), RET #err; fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hinv, Hrc⟩ HΦ
  iunfold wal.rcFile at Hrc
  icases Hrc with ⟨%f, %fd, %name, %d, Hty, Hf, Hfd⟩
  icases Hty with (%hty | ⟨%lf, %hty, #Hlf⟩)
  · unfold interface.mkOk at hty
    cases hty
    wp_apply wp_Close f fd name d $$ [Hinv Hf Hfd] as %err ⟨-, #Herr⟩
    · iframe; iexact Hinv
    iapply HΦ $$ Herr
  · unfold interface.mkOk at hty
    cases hty
    iunfold fileutil.lockedFile at Hlf
    iStructNamed Hlf
    wp_method_call
    wp_call
    (try wp_auto)
    wp_apply wp_Close f fd name d $$ [Hinv Hf Hfd] as %err ⟨-, #Herr⟩
    · iframe; iexact Hinv
    iapply HΦ $$ Herr

theorem go_etcd_io.etcd.server.v3.storage.wal.closeAll.wp_proof
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG))
    (wp_New : _root_.Perennial.errors.New.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.closeAll.spec (GF := GF) (hG := hG) := by
  intro lg sl rcs dq
  wp_start as ⟨#Hlg, #Hinv, Hsl, Hrcs⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply (wp_slice_make2 (V := GoString) (W64 0)) as %w0 ⟨Hw0, Hc0⟩
  · ipureintro; decide
  (try wp_auto)
  ihave IH : iprop(∃ (j : w64) (fv : GoInterface) (wsl : GoSlice) (ws : List GoString),
      "i" ∷ i_ptr ↦ j ∗ "f" ∷ f_ptr ↦ fv ∗ "stringArr" ∷ stringArr_ptr ↦ wsl ∗
      "Hw" ∷ wsl ↦* ws ∗ "Hwc" ∷ ownSliceCap GoString wsl (DFrac.own 1) ∗
      "Hsl" ∷ sl ↦*{dq} rcs ∗ "Hrcs" ∷ ([∗list] rc ∈ rcs.drop (sint.nat j), wal.rcFile rc) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ rcs.length⌝) $$ [i f stringArr Hw0 Hc0 Hsl Hrcs]
  · iexists W64 0, _, w0, []
    simp only [named]
    iframe
    ipureintro
    exact ⟨by decide, by simp⟩
  wp_for IH
  obtain ⟨Hj0, Hjl⟩ := Hj
  wp_if_destruct
  · have hjl : sint.nat j < rcs.length := by
      have : sint.Z j < sint.Z sl.len := Hif
      word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj0, by word⟩)]
    obtain ⟨rc, hrc⟩ : ∃ rc, rcs[sint.nat j]? = some rc := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hdrop : rcs.drop (sint.nat j) = rc :: rcs.drop (sint.nat (j + W64 1)) := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]
      rw [List.drop_eq_getElem_cons hjl]
      rw [List.getElem?_eq_getElem hjl] at hrc
      cases hrc; rfl
    wp_apply wp_load_slice_index sl (sint.Z j) rcs dq rc Hj0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hrc
    try wp_auto
    rw [hdrop]
    icases Hrcs with ⟨Hrc, Hrcs⟩
    ihave Hrc := wal.rcFile_ok rc $$ Hrc
    icases Hrc with ⟨%ii, %hii, Hrc⟩
    subst hii
    dsimp only
    wp_apply wal.wp_rcClose wp_Close ii $$ [Hrc] as %err #Herr
    · iframe; iexact Hinv
    try wp_auto
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, GoInterface.ok ii, wsl, ws
      simp only [named]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    | ok ie =>
      wp_auto
      unfold fmtErrorOkOrNil fmtErrorOk
      icases Herr with ⟨-, #Hm⟩
      rw [fmt.stringMethodSpec_unfold]
      wp_apply wp_Error as %fl -
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iexact Hlg
      try wp_auto
      try wp_auto
      wp_bind (App (Val #(methods ie.ty go!"Error" ie.v)) (Val #()))
      iapply Hm
      inext
      iintro %s
      wp_auto
      wp_apply wp_slice_literal [s]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hw $Hwc $Hsl1] as %sl' ⟨Hw, Hwc, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, GoInterface.ok ii, sl', ws ++ [s]
      simp only [named]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
  · try wp_auto
    ihave %Hwl := ownSlice_len _ _ _ $$ Hw
    wp_if_destruct
    · try wp_auto
      iapply HΦ
      iframe
      ileft
      ipureintro; rfl
    · try wp_auto
      wp_apply wp_Join $$ [Hw] as Hw
      · iframe
      wp_apply wp_New as %e ⟨-, #He⟩
      try wp_auto
      iapply HΦ
      iframe
      iright
      iexists e
      isplitr
      · ipureintro; rfl
      unfold errOk
      iintro !> %Φ' HΦ'
      iapply He
      inext
      iapply HΦ'

end proof

end EtcdGrove
end Perennial
