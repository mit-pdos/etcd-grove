/-
`grpc.KeepaliveEnforcementPolicy` (grpc-go, assumed).

Users: embed (`etcd.go:777`), `examples/lib/etcdstart`.

Why true: a client pinging too often is disconnected (its calls fail with grpc's own errors).

Changes: restored (round 1; `specs-ref/Spec/google_golang_org/grpc/KeepaliveEnforcementPolicy.lean`): a neutral option.

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

/-- `grpc.KeepaliveEnforcementPolicy(...)`: an option changing nothing the specs model. -/
def KeepaliveEnforcementPolicy.spec : Prop :=
  ∀ (ep : google_golang_org.grpc.keepalive.EnforcementPolicy),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.KeepaliveEnforcementPolicy)) (Val #ep))
  {{ (v : GoInterface), RET #v; srvOptAt v id }}

end spec

end Grpc
end EtcdGrove
end Perennial
