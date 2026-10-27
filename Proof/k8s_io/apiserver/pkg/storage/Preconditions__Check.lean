/-
Lean-first (no Rocq counterpart). The proof of `(*storage.Preconditions).Check` on `nil`: its first
branch.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.Preconditions__Check

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

theorem storage.Preconditions.Check.wp_proof :
    storage.Preconditions.Check.spec (GF := GF) (hG := hG) := by
  intro key obj
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
