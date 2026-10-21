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
`*pb.TxnRequest`, `*pb.LeaseGrantRequest`): `newBackendQuota(qa.s, qa.name).Available(r)`, over
the backend current at the check (`s.Backend()` under `s.bemu`: the fork's 8f793b820, D22g (A);
until then a quota built at construction, over a backend a snapshot's install closes), which
answers true (`apply.isQuota`, under the workload premise `apply.backendUnderQuota`, D19h, which
`quotaAlarmerAt` holds), so the NOSPACE alarm's branch (`s.MemberID()`, `s.Alarm`, then
`ErrGRPCNoSpace`) is not reached. The reader slots of `s.lgMu` and `s.bemu` (`quotaRd`) come
back. -/
abbrev v3rpc.quotaAlarmer.check.spec : Prop :=
  ∀ (qa s : Loc) (ci : GoInterfaceOk) (r : Loc) (rt : go.GoType),
  apply.quotaReqTy rt →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      v3rpc.quotaAlarmerAt qa s ∗ v3rpc.quotaRd s }}
    (App (App (Val (qa @!! go.GoType.PointerType v3rpc.quotaAlarmer.ty @!! go!"check"))
      (Val #(GoInterface.ok ci)))
      (Val #(interface.mkOk rt #r : GoInterface)))
  {{ (err : GoInterface), RET #err; v3rpc.quotaRd s }}

end spec

end EtcdGrove
end Perennial
