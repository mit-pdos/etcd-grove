/-
`openAtIndex`'s `w.tail().Name()` (write mode; W3/W5 of `notes/wal-fsext-plan.md`, twelfth session): by
then the tail's file (`os.ownFile`, its fd field whole) is the decoder's (`walFileS`), so the name is read
through the file's persistent parts only (`os.fileNamed`; `os.File.Name` reads `f.name` alone, as its
proof shows), kept from `openWALFiles`' `walOpenedFile` before the decoder takes it.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Spec.os.File__Name

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- The file `f` is named `name` (persistent: the parts of `os.ownFile` that never change). -/
def os.fileNamed (f : Loc) (name : GoString) : IProp GF :=
  iprop(∃ inner : Loc, f ↦□ (os.File.mk inner) ∗ structFieldRef os.file go!"name" inner ↦□ name)

instance os.fileNamed_persistent (f : Loc) (name : GoString) :
    Persistent (os.fileNamed (GF := GF) f name) := by
  unfold os.fileNamed; infer_instance

theorem os.ownFile_named (f : Loc) (fd : w64) (name : GoString) (dq : DFrac) :
    os.ownFile (GF := GF) f fd name dq ⊢ os.fileNamed f name := by
  unfold os.ownFile os.fileNamed
  iintro ⟨%inner, #Hf, -, #Hn⟩
  iexists inner
  isplitl [] <;> iassumption

/-- **`f.Name()` from the file's persistent parts.** -/
theorem os.File.Name.wp_named (f : Loc) (name : GoString) :
    {{ os.fileNamed (GF := GF) f name }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Name")) (Val #()))
    {{ RET #name; True }} := by
  unfold os.fileNamed
  wp_start as ⟨%inner, #Hf, #Hn⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  iapply HΦ
  iempintro

end proof

section opened
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalFs.WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- An opened file's name and lock, persistent. -/
theorem WalFs.walOpenedFile_named (write : Bool) (dir b : GoString) (i : Ino) (fr : GoInterfaceOk)
    (lf : Loc) :
    WalFs.walOpenedFile (GF := GF) write dir b i fr lf ⊢
      WalFs.walOpenedFile write dir b i fr lf ∗
      □ (∃ f : Loc, os.fileNamed f (child dir b) ∗
        (if write then fileutil.lockedFile lf f else ⌜lf = null⌝)) := by
  unfold WalFs.walOpenedFile
  cases write <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
  · iintro ⟨%f, %fd, %rl, Hf, Hfd, Ho, %hfd, %hfr, #Hrl, #Hl⟩
    ihave #Hn := os.ownFile_named f fd (child dir b) (DFrac.own 1) $$ Hf
    isplitl [Hf Hfd Ho]
    · iexists f, fd, rl
      iframe Hf Hfd Ho
      isplitr
      · ipureintro; exact hfd
      isplitr
      · ipureintro; exact hfr
      iframe #
    imodintro
    iexists f
    iframe #

end opened

end EtcdGrove
end Perennial
