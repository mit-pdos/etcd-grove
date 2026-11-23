/- Lean-first (no Rocq counterpart).

`errors.IsPathErrnoTerm.spec` proved (2026-11-22): the two-error tree of the `*PathError` (`pathErrno_walkTree`,
the `Errno`'s `Is` answering anything), over-approximated (`errorIsTree_of_walk`), at every pointer target.
-/
module

public import Spec.errors.IsPathErrnoTerm
public import Proof.errors.PathErrnoTree

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
variable [syscall.Assumptions] [os.Assumptions]

theorem errors.IsPathErrnoTerm.wp_proof : errors.IsPathErrnoTerm.spec (GF := GF) (hG := hG) := by
  intro err e he
  iintro #Hos #Hp
  ihave #Hsys : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave ⟨%xPe, %xEx, %xNE, %xUn, #Hv⟩ := errnoIsVars_of_init $$ Hsys
  ihave %hex_pe : ⌜∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe⌝ $$ []
  · iunfold os.errnoPathErr at Hp
    icases Hp with ⟨%pe, %_, %_, %h, -⟩
    ipureintro; exact ⟨pe, h⟩
  obtain ⟨pe, hpe⟩ := hex_pe
  unfold errTreeTerm
  iintro !> %u %hu
  have ht : ErrnoIsTarget u := by
    intro tii h hty
    exact (errnoIsTarget_pointer tii (hu tii h)) tii rfl hty
  iexists peS err e, (fun ii => peI err e (fun _ => True) ii true)
  isplitl
  · iapply _root_.Perennial.errors.errorIsTree_of_walk
    iapply (pathErrno_walkTree err e he u ht xPe xEx xNE xUn (fun _ => True) (fun _ _ => trivial))
    iframe #
  ipureintro
  refine ⟨Or.inl rfl, ?_⟩
  subst hpe
  refine peS_treeTyped pe e he u (fun tii h => ?_)
  obtain ⟨T, l, hT, -⟩ := hu tii h
  exact ⟨T, hT⟩

end proof

end EtcdGrove
end Perennial
