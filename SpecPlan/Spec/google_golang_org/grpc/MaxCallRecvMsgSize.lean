/-
`grpc.MaxCallRecvMsgSize` (grpc-go, assumed: `rpc_util.go`).

Users: the client's default call options (`client.go:427,433`, 1c).

Why true: a `MaxRecvMsgSizeCallOption`; a larger reply fails the call with `ResourceExhausted` (grpc's own error; the run happened).

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

/-- `grpc.MaxCallRecvMsgSize(...)`: a call option grpc's calls accept. -/
def MaxCallRecvMsgSize.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.MaxCallRecvMsgSize)) (Val #n))
  {{ (v : GoInterface), RET #v; callOptOk v }}

end spec

end Grpc
end EtcdGrove
end Perennial
