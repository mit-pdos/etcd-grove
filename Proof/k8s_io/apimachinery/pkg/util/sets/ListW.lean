/-
`List(s)` of a set of decision words (`Set[authorizer.Decision]`): a new slice of its items.
Lean-first; the second spec of `List` (the first, `List.lean`, is for strings), for the
conditional authorizer's failure messages. Its proof (unfinished). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.ListW

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem List'.wp_proofW :
    List'.specW (GF := GF) (hG := hG) := by
  sorry

end proof

end sets
end EtcdGrove
end Perennial
