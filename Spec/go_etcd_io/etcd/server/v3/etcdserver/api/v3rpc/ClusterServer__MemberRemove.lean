/-
`cs.MemberRemove(ctx, r)` (`member.go`): the Cluster service's member removal, over the server's `RemoveMember`. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20), vocabulary
`v3rpc/InvCluster.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvCluster
public import Proof.context.LibKeys

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

/-- **`cs.MemberRemove(ctx, r)`**: the server's `RemoveMember(ctx, r.ID)` (the admin guard, the
strict check and `configure`, its two callees contracts: `mayRemoveOk`, and `configureRemoveOk`,
callable only with the token `adminRes` of the request's auth info), then `togRPCError` on an error,
or the response of the header and the members `configure` returned. Each contract answers what the
handler needs as well (`memChkAns`, `memCfgAns`: an error `togRPCError` can take, the members on
`nil`). The outcome `memberOutC`: on `nil` `configure`'s answer; on an error, made by `togRPCError`
of the server's `e0`, `configure`'s answer, or `Pin` kept and the guard's refusal (`adminWhy`
relative to the caller's lower bound `n` of the auth store's published index, `Pm` kept) or the
strict check's answer `Qm e0`. -/
abbrev v3rpc.ClusterServer.MemberRemove.spec : Prop :=
  ∀ (p s cl : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (tok : Option GoString) (r : Loc) (dq : DFrac) (id : w64) (Pin Pm : IProp GF)
    (Qm : GoInterface → IProp GF) (Qin : GoSlice → GoInterface → IProp GF) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.clusterServerIs p s cl ∗ v3rpc.clusterHdrOk s cl ∗ srvAuthAt s E ∗
      □ auth.authPubLbM E.authMode n ∗ mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ E.RD ∗ Pin ∗ Pm ∗
      structFieldRef etcdserverpb.MemberRemoveRequest go!"ID" r ↦{dq} id ∗
      mayRemoveOk s id Pm (memChkAns Qm) ∗ configureRemoveOk s E ctx id Pin (memChkAns Qm) (memCfgAns Qin) }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.ClusterServer.ty @!! go!"MemberRemove"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗
      structFieldRef etcdserverpb.MemberRemoveRequest go!"ID" r ↦{dq} id ∗
      v3rpc.memberOutC Pin Qin (fun e0 => iprop((adminWhy s E.authMode n tok e0 ∗ Pm) ∨ Qm e0))
        resp err }}

end spec

end EtcdGrove
end Perennial
