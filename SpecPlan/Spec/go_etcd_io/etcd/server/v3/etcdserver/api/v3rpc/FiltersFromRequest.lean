/-
`FiltersFromRequest(creq)` (`watch.go`): mvcc's filter functions of a create request.

**Users.** `recvLoop` (`watch.go:332`); `server/proxy/grpcproxy/watch.go:272` (the gRPC proxy: not
in scope).

**Proof sketch.** Reads `creq.Filters` (a slice, read-only), appends `filterNoPut` for `NOPUT`
(`0`), `filterNoDelete` for `NODELETE` (`1`), nothing for another value, to a fresh slice.

**Changes** from `specs-ref`'s file: the exact functions (`filterFuncs`) instead of a length bound,
so that `recvLoop` can give mvcc each function's contract (`filterNoPut.spec`,
`filterNoDelete.spec`): with filters in scope (the old proof excluded them).

**Margin.** Mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`FiltersFromRequest(creq)`**: a fresh slice of the filters of the request's filter types
(`filterFuncs`). -/
def FiltersFromRequest.spec : Prop :=
  ∀ (cr : Loc) (fs : GoSlice) (fl : List w32) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      cr.[etcdserverpb.WatchCreateRequest, go!"Filters"] ↦{dq} fs ∗ fs ↦*□ fl }}
    (App (Val (@! v3rpc.FiltersFromRequest)) (Val #cr))
  {{ (sl : GoSlice), RET #sl; cr.[etcdserverpb.WatchCreateRequest, go!"Filters"] ↦{dq} fs ∗
      sl ↦* filterFuncs fl }}

end spec

end V3rpc
end EtcdGrove
end Perennial
