/-
`core/v1.Resource(resource)` (`k8s.io/api/core/v1/register.go`): the `GroupResource` of `resource`
in the core group. Names-only (a trust-boundary axiom); the spec says only that it returns.
-/
module

public import Proof.k8s_io.api.Deep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corev1

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.api.core.v1.Assumptions]

/-- **`Resource(r)`** returns (some `GroupResource`). -/
abbrev Resource.spec : Prop :=
  ∀ (r : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! k8s_io.api.core.v1.Resource)) (Val #r))
  {{ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource), RET #gr; True }}

end spec

end corev1
end EtcdGrove
end Perennial
