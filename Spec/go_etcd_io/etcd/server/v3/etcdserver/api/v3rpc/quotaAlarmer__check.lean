/-
`v3rpc.quotaAlarmer.check` (`v3rpc/quota.go`; unit P3b). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvQuota.lean`.
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

/-- **`qa.check(ctx, r)`** of a `*pb.PutRequest` `r`: the quota's `Available(r)`; if not, the
NOSPACE alarm is raised through `s.Alarm` (`EtcdServer.Alarm`: the request path's premises, an id
credit minted from the server's budget `□ |==> idCred ρ.ids 1`, `srvStarted`'s idealization)
and the error `ErrGRPCNoSpace` returned. The reader slot of `leadTimeMu` and the auth store's reader
resource `E.RD` (2026-10-14, unit A2: `Alarm`'s) come back. -/
abbrev v3rpc.quotaAlarmer.check.spec : Prop :=
  ∀ (qa s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      v3rpc.quotaAlarmerAt qa s ∗ isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
      srvLeadTimeReader s ∗ E.RD ∗ context.isContext ci cd }}
    (App (App (Val (qa @!! go.GoType.PointerType v3rpc.quotaAlarmer.ty @!! go!"check"))
      (Val #(GoInterface.ok ci)))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #r : GoInterface)))
  {{ (err : GoInterface), RET #err; srvLeadTimeReader s ∗ E.RD }}

end spec

end EtcdGrove
end Perennial
