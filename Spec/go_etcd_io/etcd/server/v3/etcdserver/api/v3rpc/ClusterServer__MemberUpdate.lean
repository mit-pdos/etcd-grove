/-
`cs.MemberUpdate(ctx, r)` (`member.go`): the Cluster service's member update, over the server's `UpdateMember`. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20), vocabulary
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

/-- **`cs.MemberUpdate(ctx, r)`**: the server's `UpdateMember(ctx, m)` of the member `m` of id
`r.ID` and peer URLs `r.PeerURLs` (borrowed, given back; the admin guard, `json.Marshal` of `m`, and
`configure` with the update change, a contract callable only with the token `adminRes` of the
request's auth info, `configureCcOk`), then `togRPCError` on an error, or the response of the header
and the members `configure` returned (`memCfgAns`: what the handler needs of its answer). The
outcome `memberOutC`: on `nil` `configure`'s answer; on an error, made by `togRPCError` of the
server's `e0`, `configure`'s answer, or `Pin` kept and the guard's refusal (`adminWhy` relative to
the caller's lower bound `n` of the auth store's published index). -/
abbrev v3rpc.ClusterServer.MemberUpdate.spec : Prop :=
  ∀ (p s cl : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (tok : Option GoString) (r : Loc) (dq : DFrac) (id : w64) (psl : GoSlice) (dp : DFrac)
    (ps : List GoString) (Pin : IProp GF) (Qin : GoSlice → GoInterface → IProp GF) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.clusterServerIs p s cl ∗ v3rpc.clusterHdrOk s cl ∗ srvAuthAt s E ∗
      □ auth.authPubLbM E.authMode n ∗ mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ E.RD ∗ Pin ∗
      structFieldRef etcdserverpb.MemberUpdateRequest go!"ID" r ↦{dq} id ∗
      structFieldRef etcdserverpb.MemberUpdateRequest go!"PeerURLs" r ↦{dq} psl ∗ psl ↦*{dp} ps ∗
      configureCcOk s E ctx (W32 2) id Pin iprop(True) (memCfgAns Qin) }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.ClusterServer.ty @!! go!"MemberUpdate"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗
      structFieldRef etcdserverpb.MemberUpdateRequest go!"ID" r ↦{dq} id ∗
      structFieldRef etcdserverpb.MemberUpdateRequest go!"PeerURLs" r ↦{dq} psl ∗ psl ↦*{dp} ps ∗
      v3rpc.memberOutC Pin Qin (fun e0 => adminWhy s E.authMode n tok e0) resp err }}

end spec

end EtcdGrove
end Perennial
