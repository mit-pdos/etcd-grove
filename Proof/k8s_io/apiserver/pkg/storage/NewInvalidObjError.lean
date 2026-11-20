/-
Lean-first (no Rocq counterpart).

The proof of `storage.NewInvalidObjError`: `errors.New` of the message (its struct
read-only, `wp_New_errorString_ro`), the composite literal.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.NewInvalidObjError

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
  wp_apply (k8s.wp_New_errorString_ro msg) as %x #Hc
  irename «$r0» => He
  generalize «$r0_ptr» = p at *
  iapply HΦ
  iexists x
  rw [show (W64 0 : w64) = 0 from rfl]
  iframe He Hc

end proof

end EtcdGrove
end Perennial
