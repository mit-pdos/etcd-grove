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

/-- **`qa.check(ctx, r)`** of a request `r` of a type `rt` with `apply.quotaReqTy rt` (`*pb.PutRequest`,
`*pb.TxnRequest`): the quota's `Available(r)`, which answers true (`apply.isQuota`, under the
workload premise `apply.backendUnderQuota`: audit phase B3, D19h, 2026-10-18), so the NOSPACE
alarm's branch (`s.Alarm`, then `ErrGRPCNoSpace`) is not reached; until then it went through the
names-only `EtcdServer.Alarm`, a false axiom (an alarm is not a request the KV model admits),
hence the precondition's id credit and reader resources, which come back unused. -/
abbrev v3rpc.quotaAlarmer.check.spec : Prop :=
  ∀ (qa s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (rt : go.GoType),
  apply.quotaReqTy rt →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      v3rpc.quotaAlarmerAt qa s ∗ isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
      srvLeadTimeReader s ∗ E.RD ∗ context.isContext ci cd }}
    (App (App (Val (qa @!! go.GoType.PointerType v3rpc.quotaAlarmer.ty @!! go!"check"))
      (Val #(GoInterface.ok ci)))
      (Val #(interface.mkOk rt #r : GoInterface)))
  {{ (err : GoInterface), RET #err; srvLeadTimeReader s ∗ E.RD }}

end spec

end EtcdGrove
end Perennial
