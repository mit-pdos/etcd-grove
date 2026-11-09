/-
`grpc.WithUnaryInterceptor` (grpc-go, assumed: `dialoptions.go`).

Users: the client's `dialSetupOpts` (`client.go:270`, 1c).

Why true: the option sets `dopts.unaryInt` to `f`, replacing any earlier one; `Invoke` then calls it (`call.go`).

Changes: from `specs-ref/Spec/google_golang_org/grpc/WithUnaryInterceptor.lean`: over `DialCfg`.

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

/-- `grpc.WithUnaryInterceptor(...)`: a dial option acting as shown. -/
def WithUnaryInterceptor.spec : Prop :=
  ∀ (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ True }}
    (App (Val (@! google_golang_org.grpc.WithUnaryInterceptor)) (Val #f))
  {{ (v : GoInterface), RET #v; dialOptAt v (fun cfg => { cfg with ui := some f }) }}

end spec

end Grpc
end EtcdGrove
end Perennial
