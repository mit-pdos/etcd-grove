/-
`v3rpc.logUnaryResponseStats` (`v3rpc/interceptor.go`, PR etcd#21401: the trust boundary of unit
P3b). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvQuota.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`logUnaryResponseStats(ctx, logFunc, duration, info, startTime, response, fields)` returns**
(PR etcd#21401): with a non-nil logger's `Debug`/`Warn` method and the call's `info` (`FullMethod`,
read-only), logs the peer (`peer.FromContext`), the method, the request ID
(`requestid.FromContext`), the duration, and the response's size and stats. -/
abbrev v3rpc.logUnaryResponseStats.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (m : GoString) (duration : time.Duration) (info : Loc)
    (startTime : time.Time) (resp : GoInterface) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      ⌜lg ≠ null⌝ ∗ ⌜m = go!"Debug" ∨ m = go!"Warn"⌝ ∗ srvInfoIs info }}
    (App (App (App (App (App (App (App (Val (@! v3rpc.logUnaryResponseStats)) (Val #ctx))
      (Val (lg @!! go.GoType.PointerType go_uber_org.zap.Logger.ty @!! m)))
      (Val #duration)) (Val #info)) (Val #startTime)) (Val #resp)) (Val #fields))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
