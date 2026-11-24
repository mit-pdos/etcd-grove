/-
`(*os.File).Close` of a shared directory fd with no error (`NoIoErr`, `notes/wal-units/noioerr.md`):
`os.File.Close.wp_dirS` (`NsS.lean`) over a semantics whose steps satisfy the premise **no I/O error on
chosen files** (every inode covered), its `DirClose` returning 0 (`wp_osDirCloseSNE`), so `Close`
returns `nil`. Lean-first.
-/
module

public import Proof.os.NsS
public import GooseLang.Ext.Fs.NoIoErrSpecs

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
variable [os.Assumptions] [go.BasicIntoValInj]

/-- **`f.Close()` of a shared directory fd, no error** (see the file header). -/
theorem os.File.Close.wp_dirSNE {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (f : Loc) (fd : w64) (name : GoString) (j : Ino) (ph : DirPhS) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗ osDirFdS fd j ph }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
    {{ RET #GoInterface.nil; emp }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  rw [decide_eq_false hnn]
  wp_auto
  ihave %hfd0 := osDirFdS_nonneg _ _ _ $$ Hosfd
  rw [decide_eq_false (by rintro rfl; exact absurd hfd0 (by decide))]
  wp_auto
  wp_apply wp_osFdKindDirS fd j ph CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  wp_apply wp_osDirCloseSNE hS fd j ph CoPset.subseteq_top $$ Hinv Hosfd
  iapply HΦ
  iempintro

end proof

end EtcdGrove
end Perennial

end
