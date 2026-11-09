/-
`metadata.AppendToOutgoingContext(ctx, kv...)` (grpc-go, assumed: `metadata/metadata.go`).

Users: Kubernetes' etcd3 client setup and `examples/etcd/auth` (a caller's own token: W0's
`ctxPrin` introduction for it is 1c's).

Why true: it panics on an odd number of arguments (excluded); else returns a `WithValue` context
whose raw metadata is the old one with the pairs appended (keys lowercased), copying the slices.

Changes: from `specs-ref/Spec/google_golang_org/grpc/metadata/AppendToOutgoingContext.lean`.

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
variable [package_sem : google_golang_org.grpc.metadata.Assumptions]

/-- `metadata.AppendToOutgoingContext(ctx, kv...)` with an even number of strings: the pairs added. -/
def AppendToOutgoingContext.spec : Prop :=
  ∀ (ctx : GoInterface) (md : MD) (sl : GoSlice) (kvs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ Context.ctxOk ctx ∗ outMD ctx md ∗ sl ↦*□ kvs ∗ ⌜kvs.length % 2 = 0⌝ }}
    (App (App (Val (@! google_golang_org.grpc.metadata.AppendToOutgoingContext)) (Val #ctx)) (Val #sl))
  {{ (ctx' : GoInterface), RET #ctx'; Context.ctxOk ctx' ∗ Context.ctxWithValues ctx ctx' ∗
      outMD ctx' (md ++ MD.ofPairs kvs) }}

end spec

end Grpc
end EtcdGrove
end Perennial
