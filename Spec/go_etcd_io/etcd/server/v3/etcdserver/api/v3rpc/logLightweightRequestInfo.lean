/-
`v3rpc.logLightweightRequestInfo` (`v3rpc/interceptor.go`, etcd#21764: the request log's entry).
Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvRequestLog.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvRequestLog

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`logLightweightRequestInfo(lg, method, remote, duration, req)` returns**, for a non-nil
logger and any decoded request (`lwReqIs req u`, read-only fields, what the type switch reads),
whatever its size: it does not panic (no nil dereference, no out-of-range index: a transaction's
first `min(len(Compare), maxLogKeys)` comparisons are read), and writes nothing of the request.
What it logs is not modeled (`zap.Logger.Info`: logging has no effect here). -/
abbrev v3rpc.logLightweightRequestInfo.spec : Prop :=
  ∀ (lg : Loc) (method remote : GoString) (duration : time.Duration) (req : GoInterface)
    (u : v3rpc.LwReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      ⌜lg ≠ null⌝ ∗ v3rpc.lwReqIs req u }}
    (App (App (App (App (App (Val (@! v3rpc.logLightweightRequestInfo)) (Val #lg)) (Val #method))
      (Val #remote)) (Val #duration)) (Val #req))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
