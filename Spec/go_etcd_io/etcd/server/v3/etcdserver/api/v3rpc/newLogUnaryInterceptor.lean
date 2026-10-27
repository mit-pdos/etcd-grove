/-
`v3rpc.newLogUnaryInterceptor` (`v3rpc/interceptor.go`; unit P3b). Lean-first (no Rocq
counterpart); the vocabulary is `Proof/google_golang_org/grpc/InvGrpc.lean` and
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`newLogUnaryInterceptor(s)`** returns a transparent interceptor (`srvInterceptorOk`, for any
requests), whose run holds a reader slot of `s.lgMu` (`s.Logger()`, after the handler): it calls
the handler and, the logger being non-nil, logs the call in a deferred `logUnaryRequestStats`
with `s.Cfg.WarningUnaryRequestDuration`. -/
abbrev v3rpc.newLogUnaryInterceptor.spec : Prop :=
  ∀ (s lg : Loc) (wd : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      srvCfgFieldAddr s go!"WarningUnaryRequestDuration" ↦□ wd }}
    (App (Val (@! v3rpc.newLogUnaryInterceptor)) (Val #s))
  {{ (ic : GoFunc), RET #ic; □ ∀ Q : GoInterface → IProp GF,
      srvInterceptorOk ic (srvLgReader s) Q }}

end spec

end EtcdGrove
end Perennial
