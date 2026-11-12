/-
Lean-first (no Rocq counterpart).

The proof of `storage.NewInvalidObjError`: `errors.New` of the message, the composite literal.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.NewInvalidObjError
public import Perennial.Proof.errors.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.NewInvalidObjError.wp_proof :
    storage.NewInvalidObjError.spec (GF := GF) (hG := hG) := by
  intro key msg
  wp_start
  wp_auto
  wp_apply (_root_.Perennial.errors.wp_New msg) as %e -
  irename «$r0» => He
  generalize «$r0_ptr» = p at *
  iapply HΦ
  iexists (GoInterface.ok e)
  rw [show (W64 0 : w64) = 0 from rfl]
  iexact He

end proof

end EtcdGrove
end Perennial
