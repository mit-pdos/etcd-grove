/-
`v3rpc.isRPCSupportedForLearner` (`server/etcdserver/api/v3rpc/`).

Users: `newUnaryInterceptor`.

Proof sketch: a type switch on the request.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/isRPCSupportedForLearner.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `isRPCSupportedForLearner(req)` of a request message of type `*t`: true for a `StatusRequest`
and a serializable `RangeRequest`, false for any other type. -/
def isRPCSupportedForLearner.spec : Prop :=
  ∀ (t : go.GoType) (q : Loc) (dq : DFrac) (c : Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ msgAt t q dq c }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isRPCSupportedForLearner)) (Val #(msgVal t q)))
  {{ (b : Bool), RET #b; msgAt t q dq c ∗
      ⌜t ≠ go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest.ty → (b = true ↔ t = go_etcd_io.etcd.api.v3.etcdserverpb.StatusRequest.ty)⌝ ∗
      ⌜∀ r, t = go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest.ty → reqModels go!"/etcdserverpb.KV/Range" c (.range r) →
        (b = true ↔ r.serializable = true)⌝ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
