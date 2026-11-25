/-
Lean-first (no Rocq counterpart).

# The union authorizer's vocabulary (`k8s.io/apiserver/pkg/authorization/union`, KEP-5681)

`isUnionAuthz h`: the handler value `union.New` returns (`unionAuthzHandler`, immutable once
built): its chain (the slice `New` was given, which it keeps) and its name-to-authorizer map are
read-only for good, and every authorizer in them is an authorizer (`authorizer.isAuthorizer`:
untrusted, whose `ConditionsAwareAuthorize` returns a well-formed decision). The chain has at most
`authorizer.authzChainMax` authorizers, named in at most `authorizer.authzNameMax` bytes (fmt stage
1: `ConditionsAwareAuthorize`'s `ToDecision` joins their decisions' reasons under their names).
Persistent.
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.union

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

/-- **The union handler** `h` (see the file header). -/
def isUnionAuthz (h : unionAuthzHandler) : IProp GF :=
  iprop(∃ (nas : List NamedAuthorizer) (m : GMap GoString GoInterface),
    h.chain' ↦*□ nas ∗ ([∗list] na ∈ nas, authorizer.isAuthorizer na.Authorizer') ∗
    h.nameToAuthorizer' ↦$□ m ∗ ([∗map] _k ↦ a ∈ m, authorizer.isAuthorizer a) ∗
    ⌜nas.length ≤ authorizer.authzChainMax ∧
      ∀ na ∈ nas, na.AuthorizerName'.length ≤ authorizer.authzNameMax⌝)

instance isUnionAuthz_persistent (h : unionAuthzHandler) :
    Persistent (isUnionAuthz (GF := GF) h) := by
  unfold isUnionAuthz; infer_instance

end defs

end union
end EtcdGrove
end Perennial
