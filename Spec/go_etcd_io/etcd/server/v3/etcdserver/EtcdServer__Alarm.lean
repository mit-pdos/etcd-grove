/-
`s.Alarm(ctx, r)` (`v3_server.go`, names-only: the trust boundary of unit P3b). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Alarm(ctx, r)` returns** (the quota wrapper's NOSPACE alarm, `quotaAlarmer.check`):
`Alarm` is `s.raftRequest(ctx, &pb.InternalRaftRequest{Alarm: r})` and a type assertion of the
response; its premises are `raftRequest`'s for a request goroutine (the request path's view
`isServerReq`, a reader slot of `leadTimeMu`, given back, an id credit, the request's context)
and the alarm request, owned. What the alarm does (the apply thread's `AlarmStore`) is not
stated: the quota wrapper ignores the answer. -/
abbrev EtcdServer.Alarm.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ci cd ∗
      (∃ v : etcdserverpb.AlarmRequest, p ↦ v) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Alarm"))
      (Val #(GoInterface.ok ci))) (Val #p))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD }}

end spec

end EtcdGrove
end Perennial
