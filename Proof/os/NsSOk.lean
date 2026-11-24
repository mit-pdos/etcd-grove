/-
`os.OpenFile`/`os.Open` read-only of a directory in the tree's shared mode (`NsS.lean`'s
`wp_dirS`), with the error's `fmtErrorOkOrNil` (the `*PathError`'s `Error()`, `os.wp_pathError_ok`),
as `wp_fileS`'s error arm has it: for callers wrapping the error with `%w` (`wal.Open`'s
`fileutil.OpenDir`, 2026-11-14). Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.IgnoringEINTR
public import Proof.os.NsS

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

theorem os.OpenFile.wp_dirSOk (p : GoString) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac)
    (qc : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm (callKey R p) qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm (callKey R p) qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osDirFdS fd j .idle) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }} := by
  wp_start_folded as ⟨#Hos, #Hsi, Hp, Hperm⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  wp_apply os.OpenFile.wp_dirErrS p perm R j dq qc $$ [Hos Hsi Hp Hperm] as %f %err ⟨Hp, Hperm, Hr⟩
  · iframe; (repeat' isplitl []) <;> iassumption
  iapply HΦ
  iframe Hp Hperm
  icases Hr with (Hok | ⟨%e, %he, #Herr⟩)
  · ileft; iexact Hok
  · iright
    ihave %hne := (os.errnoPathErr_ne err e) $$ Herr
    isplitr
    · ipureintro; exact ⟨hne, he.2⟩
    · iapply (os.errnoPathErr_fmtErrorOkOrNil err e he.1) $$ Hsys Herr

/-- `os.Open(p)` of the directory `j`: `OpenFile(p, O_RDONLY, 0)`. -/
theorem os.Open.wp_dirSOk (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm (callKey R p) qc }}
      (App (Val (@! os.Open)) (Val #p))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm (callKey R p) qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osDirFdS fd j .idle) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }} := by

  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  try wp_auto
  wp_apply os.OpenFile.wp_dirSOk p (W32 0) R j dq qc $$ [Hinv Hsi Hp Hperm] as %f %err Hr
  · iframe; (repeat' isplitl []) <;> iassumption
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial
