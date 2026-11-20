/-
`ConditionsAwareDecisionFromParts(dec, reason, err)` (`conditions.go`): the unconditional decision
of the word `dec` (Deny for a word other than the three, with an aggregated error). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- See the file header. -/
abbrev ConditionsAwareDecisionFromParts.spec : Prop :=
  ∀ (k : w64) (r : GoString) (e : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer }}
    (App (App (App (Val (@! ConditionsAwareDecisionFromParts)) (Val #k)) (Val #r)) (Val #e))
  {{ (d : ConditionsAwareDecision), RET #d; isDecision d (Dec.ofWord k) }}

end spec

end authorizer
end EtcdGrove
end Perennial
