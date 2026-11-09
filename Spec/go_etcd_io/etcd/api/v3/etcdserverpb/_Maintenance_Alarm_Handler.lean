/-
`_Maintenance_Alarm_Handler(srv, ctx, dec, interceptor)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the
server-side handler of `/etcdserverpb.Maintenance/Alarm`.

Users: grpc's `Serve` (2a: `regsOk`, from `Maintenance_ServiceDesc`'s `MethodDesc`, `otherDescs_init`), for the
service value `v3rpc` registers (`RegisterMaintenanceServer`); the method is 2a's `authMaintenanceServer.Alarm`.
Proof sketch: `new(AlarmRequest)` (a fresh message: some content), `dec(in)` (`Grpc.decOk_call`: the
request's content, canonical, no error), then `handlerBodyWP`: the type assertion `srv.(MaintenanceServer)`
(the premise), the method directly or through the interceptor (with a `*UnaryServerInfo` and the
closure calling the method). 2a composes it with `icChain_call` and the method's `HandlerTriple`
into `Grpc.unaryOk`. Blocked: the body is untranslated (names only in `Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`): the proof waits for its translation (open question 7.4).
Changes: verify-round: new (A6 completeness F1 / provability F9: a registered handler had no spec),
in the form of the translated handlers (`_Auth_UserAdd_Handler.spec`), the decoded request
canonical (`⌜Proto.norm c = c⌝`, A6 F2).
Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `_Maintenance_Alarm_Handler(srv, ctx, dec, ic)`: decode the request, then run `handlerBodyWP` (WP form). -/
def _Maintenance_Alarm_Handler.spec : Prop :=
  ∀ (srv : GoInterfaceOk) (ctx : GoInterface) (dec : val) (ic : GoFunc) (c : Proto.Content)
    (Ψ : val → IProp GF),
  go.typeSetContains srv.ty etcdserverpb.MaintenanceServer.ty = true →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ Grpc.decOk dec etcdserverpb.AlarmRequest.ty c ∗
    (∀ q : Loc, Proto.msgAt etcdserverpb.AlarmRequest.ty q (DFrac.own 1) c -∗ ⌜Proto.norm c = c⌝ -∗
      handlerBodyWP srv go!"Alarm" etcdserverpb.AlarmRequest.ty etcdserverpb.AlarmResponse.ty go!"/etcdserverpb.Maintenance/Alarm"
        ctx q ic Ψ) ⊢
  WP (App (App (App (App (Val (@! etcdserverpb._Maintenance_Alarm_Handler)) (Val #(GoInterface.ok srv)))
    (Val #ctx)) (Val dec)) (Val #ic)) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
