/-
`cs.MemberAdd(ctx, r)` (`member.go`): the Cluster service's member addition, over the server's `AddMember`. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20), vocabulary
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

/-- **`cs.MemberAdd(ctx, r)`**: `types.NewURLs(r.PeerURLs)`, the member (`NewMemberAsLearner` when
`r.IsLearner`, `NewMember` otherwise: names only, the contract `newMemberOk`), the server's
`AddMember(ctx, *m)` (the admin guard, the strict check and `configure`, both callees contracts:
`mayAddOk` of any member, and `configureCcOk` of the member's change of any id, callable only with
the token `adminRes` of the request's auth info), then `togRPCError` on an error, or the response
of the header, the member and the members `configure` returned. Each contract answers what the
handler needs as well (`memChkAns`, `memCfgAns`). The outcome `memberOutC`, as `MemberRemove`'s.

**The margin** (decided by etcd-grove-03, 2026-11-20): the request's peer URLs are a non-empty list
of plain `http://host:port` URLs (`types.plainPeerURL`), what `types.NewURLs`' trust-boundary spec
covers; another request (a bad URL: `ErrGRPCMemberBadURLs`; `https`, a path, an empty list) is not
covered. -/
abbrev v3rpc.ClusterServer.MemberAdd.spec : Prop :=
  ∀ (p s cl : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (tok : Option GoString) (r : Loc) (dq : DFrac) (psl : GoSlice) (ps : List GoString)
    (lrn : Bool) (Pin Pm : IProp GF) (Qm : GoInterface → IProp GF)
    (Qin : GoSlice → GoInterface → IProp GF) (n : Nat),
  ps ≠ [] → (∀ u ∈ ps, types.plainPeerURL u) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.clusterServerIs p s cl ∗ v3rpc.clusterHdrOk s cl ∗ srvAuthAt s E ∗
      □ auth.authPubLbM E.authMode n ∗ mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ E.RD ∗ Pin ∗ Pm ∗
      structFieldRef etcdserverpb.MemberAddRequest go!"PeerURLs" r ↦{dq} psl ∗ psl ↦*{dq} ps ∗
      structFieldRef etcdserverpb.MemberAddRequest go!"IsLearner" r ↦{dq} lrn ∗
      v3rpc.newMemberOk ∗
      (∀ (memb : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member) (mps : List GoString),
        mayAddOk s memb (DFrac.own 1) (DFrac.own 1) mps [] Pm (memChkAns Qm)) ∗
      (∀ id : w64, configureCcOk s E ctx (addChangeType lrn) id Pin (memChkAns Qm GoInterface.nil)
        (memCfgAns Qin)) }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.ClusterServer.ty @!! go!"MemberAdd"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗
      structFieldRef etcdserverpb.MemberAddRequest go!"PeerURLs" r ↦{dq} psl ∗ psl ↦*{dq} ps ∗
      structFieldRef etcdserverpb.MemberAddRequest go!"IsLearner" r ↦{dq} lrn ∗
      v3rpc.memberOutC Pin Qin (fun e0 => iprop((adminWhy s E.authMode n tok e0 ∗ Pm) ∨ Qm e0))
        resp err }}

end spec

end EtcdGrove
end Perennial
