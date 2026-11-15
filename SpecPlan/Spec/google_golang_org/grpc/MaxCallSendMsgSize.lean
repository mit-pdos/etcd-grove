/-
`grpc.MaxCallSendMsgSize` (grpc-go, assumed: `rpc_util.go`).

Users: the client's default call options (`client.go:426,430`, 1c).

Why true: a `MaxSendMsgSizeCallOption`; a larger request fails with `ResourceExhausted` before it is sent (grpc's own error).

Changes: new.

Margin: the option's effect (waiting, limits) is not modelled: a call with it may fail with an
error grpc makes itself (`ownErr`), which every call spec allows.
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

/-- `grpc.MaxCallSendMsgSize(...)`: a call option grpc's calls accept. -/
def MaxCallSendMsgSize.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.MaxCallSendMsgSize)) (Val #n))
  {{ (v : GoInterface), RET #v; callOptOk v }}

end spec

end Grpc
end EtcdGrove
end Perennial
