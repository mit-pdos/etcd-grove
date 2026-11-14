/-
`os.OpenFile`/`os.Open` read-only of a directory in the tree's shared mode (`NsS.lean`'s
`wp_dirS`), with the error's `fmtErrorOkOrNil` (the `*PathError`'s `Error()`, `os.wp_pathError_ok`),
as `wp_fileS`'s error arm has it: for callers wrapping the error with `%w` (`wal.Open`'s
`fileutil.OpenDir`, 2026-11-14). Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.NsS

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
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

theorem os.OpenFile.wp_dirSOk (p : GoString) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac)
    (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osDirFdS fd j .idle) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp HΦ
  wp_apply wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  (try wp_auto)
  wp_apply wp_osOpenDirS R p j dq t s0 qc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hp Hk as %fd %e %hres Hperm Hp Hfd
  by_cases he0 : e = W64 0
  · subst he0
    ihave Hfd := Hfd $$ %rfl
    rw [decide_eq_true rfl]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; rfl
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · iclear Hfd
    rw [decide_eq_false he0]
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hperm Hp HΦ
    · rw [decide_eq_false he4]
      wp_auto
      wp_apply os.wp_pathError_ok _ _ e he0 as %pe #Hok
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok

/-- `os.Open(p)` of the directory `j`: `OpenFile(p, O_RDONLY, 0)`. -/
theorem os.Open.wp_dirSOk (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm qc }}
      (App (Val (@! os.Open)) (Val #p))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osDirFdS fd j .idle) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }} := by
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm⟩
  wp_auto
  wp_apply os.OpenFile.wp_dirSOk p (W32 0) R j dq qc $$ [Hinv Hsi Hp Hperm] as %f %err Hr
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial
