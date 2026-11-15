/-
`v3rpc.header.fill` (`server/etcdserver/api/v3rpc/`).

Users: every handler of this package (`hdr.fill(resp.Header)`), `headerFillingRangeStream.Send`, the maintenance snapshots.

Proof sketch: the getters of the server (2d: `Term`, `Leader`; 3e: `KV().Rev()`, `KV()` through `isServer_kv`'s `s.kv ↦□ w` and `EtcdServer.KV.spec` at it), field writes; a `nil` header panics (excluded: `respHeaderOwn` is of a non-nil pointer).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/header__fill.lean`: over W0's `respHeaderOwn`.
verify-round relay (server-core's RR request 3): `KV()` through `isServer_kv` (2c's `KV.spec` now takes the points-to).

Margin: the ids, term and leader are not modelled (W0's replies relate only the revision).
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

/-- `h.fill(rh)` on an owned header: the ids, term and leader filled, the revision kept unless it is `0` (then the store's current one). -/
def header.fill.spec : Prop :=
  ∀ (hp : Loc) (h : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header) (s : Loc) (γ : Cluster) (rh : Loc) (m : HeaderM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ hp ↦□ h ∗ headerAt h s γ ∗ respHeaderOwn rh (DFrac.own 1) m }}
    (App (Val (hp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header.ty @!! go!"fill")) (Val #rh))
  {{ RET #(); ∃ m', respHeaderOwn rh (DFrac.own 1) m' ∗
      ⌜m.revision ≠ W64 0 → m'.revision = m.revision⌝ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
