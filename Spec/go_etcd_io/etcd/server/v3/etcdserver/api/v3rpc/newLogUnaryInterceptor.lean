/-
`v3rpc.newLogUnaryInterceptor` (`v3rpc/interceptor.go`; unit P3b, updated for PR etcd#21401).
Lean-first (no Rocq counterpart); the vocabulary is `Proof/google_golang_org/grpc/InvGrpc.lean` and
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

/-- **`newLogUnaryInterceptor(s)`** (PR etcd#21401) returns an interceptor (`srvInterceptorOk`, for
requests satisfying `learnerReqOk`), whose run holds a reader slot of `s.lgMu` (`s.Logger()`): it
generates a fresh request ID via `s.RequestID()`, attaches it to `ctx` via
`requestid.NewContext(ctx, requestID)` (establishing `reqIdCtxAt γi ci'` and thus `C ci'`), checks
`lg.Core().Enabled(zap.DebugLevel)` (note: PR etcd#21401 removed the `if lg != nil` guard), logs the
request on debug via `logUnaryRequest`, invokes the handler with the enriched `ctx`, and logs
response stats via `logUnaryResponseStats` (calling `requestLogFields(req)` when `!debug` and slow). -/
abbrev v3rpc.newLogUnaryInterceptor.spec : Prop :=
  ∀ (s lg : Loc) (wd : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      srvCfgFieldAddr s go!"WarningUnaryRequestDuration" ↦□ wd }}
    (App (Val (@! v3rpc.newLogUnaryInterceptor)) (Val #s))
  {{ (ic : GoFunc), RET #ic;
      □ ∀ (γi : IdNames) (C : GoInterfaceOk → IProp GF),
        srvIdGen s γi -∗ idCred γi 1 -∗ □ (∀ ci', reqIdCtxAt γi ci' -∗ C ci') -∗
        srvInterceptorOk ic (srvLgReader s) v3rpc.learnerReqOk C }}

end spec

end EtcdGrove
end Perennial
