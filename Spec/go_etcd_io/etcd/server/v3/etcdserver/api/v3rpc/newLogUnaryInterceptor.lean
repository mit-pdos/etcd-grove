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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The log interceptor stores the client's address** (PR etcd#22259): `ic`, called (with `R`)
on a run context whose peer is at `o` (`grpcRunPeerIs`), calls the handler on a run context that,
when there is a peer (`o = some addr`), carries `addr` as its client IP (`auth.ctxClientIPIs ci'
(some addr)`: what `ClientIPFromContext` downstream returns), or returns `(nil, err)` without
calling it; `R` comes back. `srvInterceptorOk` with the client IP in the handler's context. -/
def v3rpc.logIcStoresIP (ic : GoFunc) (R : IProp GF) (Q : GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (req : GoInterface)
      (info : Loc) (h : GoFunc) (Ψ : val → IProp GF) (o : Option GoString),
    R -∗ context.isContext ci cd -∗ grpcRunCtx ci -∗ grpcRunPeerIs ci o -∗ srvInfoIs info -∗
    □ Q req -∗
    ((∀ (ci' : GoInterfaceOk) (cd' : context.ContextDesc (IProp GF)),
        context.isContext ci' cd' -∗ grpcRunCtx ci' -∗
        (match o with
         | some addr => auth.ctxClientIPIs ci' (some addr)
         | none => iprop(True)) -∗
        WP (srvHandlerCall h #(GoInterface.ok ci') #req)
          {{ v, ∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗ (R -∗ Ψ v) }}) ∧
      (R -∗ ∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗
        Ψ (PairV #GoInterface.nil #err))) -∗
    WP (srvInterceptorCall ic #(GoInterface.ok ci) #req #info h) {{ Ψ }})

instance v3rpc.logIcStoresIP_persistent (ic : GoFunc) (R : IProp GF) (Q : GoInterface → IProp GF) :
    Persistent (v3rpc.logIcStoresIP (GF := GF) ic R Q) := by
  unfold v3rpc.logIcStoresIP; infer_instance

/-- **`newLogUnaryInterceptor(s)`** returns a transparent interceptor (`srvInterceptorOk`, for any
requests), whose run holds a reader slot of `s.lgMu` (`s.Logger()`, after the handler): it calls
the handler and, the logger being non-nil, logs the call in a deferred `logUnaryRequestStats`
with `s.Cfg.WarningUnaryRequestDuration`. Since PR etcd#22259 it first stores the run's peer
address in the context it hands the handler (`v3rpc.logIcStoresIP`). -/
abbrev v3rpc.newLogUnaryInterceptor.spec : Prop :=
  ∀ (s lg : Loc) (wd : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      srvCfgFieldAddr s go!"WarningUnaryRequestDuration" ↦□ wd }}
    (App (Val (@! v3rpc.newLogUnaryInterceptor)) (Val #s))
  {{ (ic : GoFunc), RET #ic; □ ∀ Q : GoInterface → IProp GF,
      srvInterceptorOk ic (srvLgReader s) Q ∗ v3rpc.logIcStoresIP ic (srvLgReader s) Q }}

end spec

end EtcdGrove
end Perennial
