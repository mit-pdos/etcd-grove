/-
The proof of `Spec/os/File__CloseLe.lean`: `File__Close.lean`'s, with the message bound of
`os.wp_wrapErrno_okLe`.
-/
module

public import Spec.os.File__CloseLe
public import Proof.os.ErrorOk
public import GooseLang.Ext.Fs.NoMapLockErrSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- `os.File.Close.spec` without the error witness (session S6: a helper of the proof below). -/
private abbrev os.File.Close.tripleOldLe : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (d : OsFd),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) d ∗ lockToks (GF := GF) fd d }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f (-1 : w64) name (DFrac.own 1) ∗
      fmtErrorOkOrNilLe (os.closeErrMax name) err }}

/-- `os.File.Close.spec` over a semantics with no errors (the former `os.File.Close.specNoErr`). -/
private abbrev os.File.Close.tripleNELe : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (f : Loc) (fd : w64) (name : GoString) (d : OsFd),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) d ∗ lockToks (GF := GF) fd d }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
  {{ RET #(interface.nil : GoInterface); os.ownFile f (-1 : w64) name (DFrac.own 1) }}

private theorem os.File.Close.wp_oldLe : os.File.Close.tripleOldLe (GF := GF) (hG := hG) := by
  intro f fd name d
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb, #Hap, #Hsys⟩, Hosfd, Hlt⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  try wp_auto
  rw [decide_eq_false hnn]
  try wp_auto
  ihave %hfd0 := osFd_nonneg _ _ _ $$ Hosfd
  rw [decide_eq_false (show fd ≠ W64 (-1) by rintro rfl; exact absurd hfd0 (by decide))]
  try wp_auto
  try wp_auto
  wp_stub os.fsFdKind.impl
  wp_apply wp_osFdKind fd (DFrac.own 1) d CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  try wp_auto
  wp_stub os.fsClose.impl
  wp_apply wp_osClose fd d CoPset.subseteq_top $$ [Hinv Hosfd Hlt] as %e -
  · iframe; iexact Hinv
  by_cases he : e = W64 0
  · rw [decide_eq_true he]
    try wp_auto
    iapply HΦ
    isplitl
    · iexists inner
      iframe
      (repeat' isplitl []) <;> iassumption
    unfold fmtErrorOkOrNilLe
    itrivial
  · rw [decide_eq_false he]
    try wp_auto
    wp_apply os.wp_wrapErrno_okLe _ inner name e he $$ Hn Hsys as %pe #Hok
    iapply HΦ
    isplitl
    · iexists inner
      iframe
      (repeat' isplitl []) <;> iassumption
    unfold fmtErrorOkOrNilLe os.closeErrMax
    iapply fmtErrorOkLe_mono _ _ $$ Hok
    simp only [show (go!"close" : GoString).length = 5 from rfl]
    omega

private theorem os.File.Close.wp_NELe : os.File.Close.tripleNELe (GF := GF) (hG := hG) := by
  intro Sio _ hS f fd name d
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb, #Hap, #Hsys⟩, Hosfd, Hlt⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  try wp_auto
  rw [decide_eq_false hnn]
  try wp_auto
  ihave %hfd0 := osFd_nonneg _ _ _ $$ Hosfd
  rw [decide_eq_false (show fd ≠ W64 (-1) by rintro rfl; exact absurd hfd0 (by decide))]
  try wp_auto
  try wp_auto
  wp_stub os.fsFdKind.impl
  wp_apply wp_osFdKind fd (DFrac.own 1) d CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  try wp_auto
  wp_stub os.fsClose.impl
  wp_apply wp_osCloseNE hS fd d CoPset.subseteq_top $$ [Hinv Hosfd Hlt]
  · iframe; iexact Hinv
  iapply HΦ
  iexists inner
  iframe
  (repeat' isplitl []) <;> iassumption

/-- **`Close.specLe`**: by cases on `FsNoErr`, the error-free triple (`nil`) or the one without the
witness. -/
theorem os.File.Close.wp_proofLe : os.File.Close.specLe (GF := GF) (hG := hG) := by
  intro f fd name d
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs1
    iapply os.File.Close.wp_NELe Sio hSio f fd name d $$ Hpre
    inext
    iintro Hfo
    iapply HΦ
    iframe Hfo
    isplitl []
    · ipureintro; left; rfl
    unfold fmtErrorOkOrNilLe
    itrivial
  · iapply os.File.Close.wp_oldLe f fd name d $$ Hpre
    inext
    iintro %err ⟨Hfo, #Hok⟩
    iapply HΦ
    iframe Hfo Hok
    ipureintro; right; exact hne

end proof

end EtcdGrove
end Perennial
