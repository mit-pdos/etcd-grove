/-
Lean-first (no Rocq counterpart).

The proof of `storage.NewKeyExistsError`: the composite literal.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.NewKeyExistsError

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

theorem storage.NewKeyExistsError.wp_proof :
    storage.NewKeyExistsError.spec (GF := GF) (hG := hG) := by
  intro key rv
  wp_start
  wp_auto
  wp_alloc e as He
  wp_auto
  iapply HΦ
  iexact He

end proof

end EtcdGrove
end Perennial
