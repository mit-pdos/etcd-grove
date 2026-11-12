/-
`grpc.WithStreamInterceptor` (grpc-go, assumed: `dialoptions.go`).

Users: the client's `dialSetupOpts` (`client.go:269`, 1c).

Why true: the option sets `dopts.streamInt`; `NewStream` then calls it (`stream.go`).

Changes: from `specs-ref/.../grpc/WithStreamInterceptor.lean`: over `DialCfg`.

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

/-- `grpc.WithStreamInterceptor(...)`: a dial option acting as shown. -/
def WithStreamInterceptor.spec : Prop :=
  ∀ (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ True }}
    (App (Val (@! google_golang_org.grpc.WithStreamInterceptor)) (Val #f))
  {{ (v : GoInterface), RET #v; dialOptAt v (fun cfg => { cfg with si := some f }) }}

end spec

end Grpc
end EtcdGrove
end Perennial
