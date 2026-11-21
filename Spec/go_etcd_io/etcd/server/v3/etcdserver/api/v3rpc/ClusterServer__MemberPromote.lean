/-
`cs.MemberPromote(ctx, r)` (`member.go`): the Cluster service's promotion of a learner, over the
server's `PromoteMember`. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20), vocabulary
`v3rpc/InvCluster.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvCluster
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
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

/-- **`cs.MemberPromote(ctx, r)`**: the server's `PromoteMember(ctx, r.ID)` (the admin guard, the
strict check and `configure`, both callees contracts: `mayPromoteOk`, and `configureCcOk`, callable
only with the token `adminRes` of the request's auth info; off the leader, the forwarding to it,
`promoteMemberHTTP` a contract `promoteHTTPOk` whose answer is the leader's re-check `Qfw`), then
`togRPCError` on an error, or the response of the header and the members returned. Each contract
answers what the handler needs as well (`memChkAns`, `memCfgAns`: an error `togRPCError` can take,
whose message is valid UTF-8, the members on `nil`). The outcome: an error grpc's server takes
(`srvErrOk`); on `nil` `configure`'s answer `Qin` or the leader's `Qfw`; on an error (and no
response), one `togRPCError` made of a server error `e0`. Nothing more is stated of an error: an
error of the forwarding (the leader's refusal, `waitLeader`'s, the forwarding's timeout) carries
nothing, unlike `memberOutC`'s (`MemberRemove`), whose errors carry `configure`'s answer or the
guard's refusal (`adminWhy`) with `Pin` kept. -/
abbrev v3rpc.ClusterServer.MemberPromote.spec : Prop :=
  ∀ (p s cl : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (tok : Option GoString) (r : Loc) (dq : DFrac) (id : w64)
    (Pin Pm : IProp GF) (Qm : GoInterface → IProp GF) (Qin Qfw : GoSlice → GoInterface → IProp GF)
    (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.clusterServerIs p s cl ∗ v3rpc.clusterHdrOk s cl ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvPeerRt s ∗ srvAuthAt s E ∗
      □ auth.authPubLbM E.authMode n ∗ context.isContext ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ E.RD ∗ Pin ∗ Pm ∗
      structFieldRef etcdserverpb.MemberPromoteRequest go!"ID" r ↦{dq} id ∗
      mayPromoteOk s id Pm (memChkAns Qm) ∗
      configureCcOk s E ctx (W32 0) id Pin (memChkAns Qm GoInterface.nil) (memCfgAns Qin) ∗
      promoteHTTPOk id (memCfgAns Qfw) }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.ClusterServer.ty @!! go!"MemberPromote"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗
      structFieldRef etcdserverpb.MemberPromoteRequest go!"ID" r ↦{dq} id ∗
      go_etcd_io.etcd.cache.v3.srvErrOk err ∗
      ((⌜err = GoInterface.nil⌝ ∗
          ((∃ sl : GoSlice, Qin sl GoInterface.nil) ∨ (∃ sl : GoSlice, Qfw sl GoInterface.nil))) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e0 : GoInterface, ⌜e0 ≠ GoInterface.nil⌝ ∗
          v3rpc.grpcErrOut (fun _ => True) e0 err)) }}

end spec

end EtcdGrove
end Perennial
