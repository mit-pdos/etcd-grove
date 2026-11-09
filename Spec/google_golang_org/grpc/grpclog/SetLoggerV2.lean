/-
`grpclog.SetLoggerV2(l)` (grpc-go, assumed: `grpclog/loggerv2.go`, names only here).

Users: Kubernetes' `etcd3` package initializer (`staging/src/k8s.io/apiserver/pkg/storage/etcd3/
logger.go:27`, a `klogWrapper`), before any client is built.

Why true: it stores `l` as grpc's logger (`internal/grpclog`'s package variables, written without
synchronization: grpc documents it as to be called before any other grpc function, which the
initializer's position ensures) and returns; it reads nothing of `l`.

Changes: verify-round: restored (A6 completeness F6: dropped from the old tree,
`specs-ref/Spec/google_golang_org/grpc/grpclog/SetLoggerV2.lean`), over the package's `isPkgInit`.
Margin: none (nothing the specs model changes).
-/
module

public import Spec.google_golang_org.grpc.Api
public import GeneratedProof.google_golang_org.grpc.grpclog
public import Spec.PkgInit.google_golang_org.grpc.grpclog

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

/-- `grpclog.SetLoggerV2(l)`: returns. -/
def grpclog.SetLoggerV2.spec : Prop :=
  ∀ (l : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.grpclog }}
    (App (Val (@! google_golang_org.grpc.grpclog.SetLoggerV2)) (Val #l))
  {{ RET #(); True }}

end spec

end Grpc
end EtcdGrove
end Perennial
