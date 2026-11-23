/- Lean-first (no Rocq counterpart).

`errors.IsErrno.spec` proved (2026-11-22): the tree of the `Errno` alone (`errno_walkTree`), at a target `Errno`,
which `==` compares as `uintptr`s (`comparableErr_uintptr`), over Perennial's `errors.wp_Is`.
-/
module

public import Spec.errors.IsErrno
public import Proof.errors.PathErrnoTree
public import Perennial.Proof.errors.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [syscall.Assumptions] [_root_.Perennial.errors.Assumptions]

theorem errors.IsErrno.wp_proof : errors.IsErrno.spec (GF := GF) (hG := hG) := by
  intro e t he
  iintro %Φ ⟨#Herr, #Hsys⟩ HΦ
  ihave ⟨%xPe, %xEx, %xNE, %xUn, #Hv⟩ := errnoIsVars_of_init $$ Hsys
  have ht : ErrnoIsTarget (interface.mkOk syscall.Errno.ty #t) := by
    apply errnoIsTarget_not_es
    intro tii h
    cases h
    exact errno_ne_ptr _
  ihave #Htree := errno_walkTree e he _ ht xPe xEx xNE xUn $$ Hv
  have hen : errnoErr e = interface.mkOk syscall.Errno.ty #e := by
    unfold errnoErr; simp only [he, ↓reduceIte]
  have hc : _root_.Perennial.errors.ComparableTarget (· = errnoErr e) (interface.mkOk syscall.Errno.ty #t) := by
    intro tii h
    cases h
    refine _root_.Perennial.errors.comparableErr_uintptr _ _ t rfl ?_
    intro ii hii _
    rw [hen] at hii; cases hii
    exact ⟨e, rfl⟩
  wp_apply +noauto _root_.Perennial.errors.wp_Is (· = errnoErr e) _ _ (errnoErr e) _ hc $$ [$Herr $Htree]
    as %b -
  · ipureintro; rfl
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
