/-
`grpc.WithPerRPCCredentials` (grpc-go, assumed: `dialoptions.go`).

Users: the client's `dial` (`client.go:322`, 1c: the token bundle).

Why true: the option appends `pc` to `dopts.copts.PerRPCCredentials`; every call and stream adds the metadata of each, in order (`http2_client.go`, `createHeaderFields`).

Changes: from `specs-ref/.../grpc/WithPerRPCCredentials.lean`: the metadata as `R`.

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api

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

/-- `grpc.WithPerRPCCredentials(...)`: a dial option acting as shown. -/
def WithPerRPCCredentials.spec : Prop :=
  ∀ (pc : GoInterface) (R : MD → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ perRPCAt pc R }}
    (App (Val (@! google_golang_org.grpc.WithPerRPCCredentials)) (Val #pc))
  {{ (v : GoInterface), RET #v; dialOptAt v (fun cfg => { cfg with R := fun md => iprop(∃ m1 m2, ⌜md = m1 ++ m2⌝ ∗ cfg.R m1 ∗ R m2) }) }}

end spec

end Grpc
end EtcdGrove
end Perennial
