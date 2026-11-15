/-
`grpc.WithResolvers` (grpc-go, assumed: `dialoptions.go`).

Users: the client's `dialWithBalancer`, `dialWithBalancerCreds` (`client.go:282,313`, 1c).

Why true: the client connection resolves the target with the given builder (its scheme), and dials only the addresses its resolver reports (`resolver_wrapper.go`); etcd's target uses its resolver's scheme. Passed as a slice of one builder in etcd: the spec is for one.

Changes: from `specs-ref/.../grpc/WithResolvers.lean`: the addresses as `A`.

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.WithResolvers(...)`: a dial option acting as shown. -/
def WithResolvers.spec : Prop :=
  ∀ (r : GoInterface) (A : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ resolverAt r A }}
    (App (Val (@! google_golang_org.grpc.WithResolvers)) (Val #r))
  {{ (v : GoInterface), RET #v; dialOptAt v (fun cfg => { cfg with A := A }) }}

end spec

end Grpc
end EtcdGrove
end Perennial
