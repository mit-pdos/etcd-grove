/-
The proof of `Spec/os/File__CloseNoErr.lean`: a store of -1 to the fd field, and `wp_osCloseNE`.
-/
module

public import Spec.os.File__CloseNoErr
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

theorem os.File.Close.wp_proofNoErr : os.File.Close.specNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS f fd name d
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hlt⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  rw [decide_eq_false hnn]
  wp_auto
  ihave %hfd0 := osFd_nonneg _ _ _ $$ Hosfd
  rw [decide_eq_false (by rintro rfl; exact absurd hfd0 (by decide))]
  wp_auto
  wp_apply wp_osFdKind fd (DFrac.own 1) d CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  wp_apply wp_osCloseNE hS fd d CoPset.subseteq_top $$ [Hinv Hosfd Hlt]
  · iframe; iexact Hinv
  iapply HΦ
  iexists inner
  iframe
  isplitl [] <;> iassumption

end proof

end EtcdGrove
end Perennial
