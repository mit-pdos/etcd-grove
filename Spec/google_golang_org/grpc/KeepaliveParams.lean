/-
`grpc.KeepaliveParams` (grpc-go, assumed).

Users: embed (`etcd.go:784`), `examples/lib/etcdstart`.

Why true: server-side pings and connection ages close transports; runs see their contexts done.

Changes: restored (round 1; `specs-ref/Spec/google_golang_org/grpc/KeepaliveParams.lean`): a neutral option.

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api
public import GeneratedProof.google_golang_org.grpc.keepalive

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

/-- `grpc.KeepaliveParams(...)`: an option changing nothing the specs model. -/
def KeepaliveParams.spec : Prop :=
  ∀ (kp : google_golang_org.grpc.keepalive.ServerParameters),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.KeepaliveParams)) (Val #kp))
  {{ (v : GoInterface), RET #v; srvOptAt v id }}

end spec

end Grpc
end EtcdGrove
end Perennial
