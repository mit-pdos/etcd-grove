/-
`(*EtcdServer).MemberList(ctx, r)` (`server.go:1693-1704`): with `r.Linearizable`, a linearizable
read barrier (`s.read.LinearizableReadNotify`); then `requireAuthInfo`; then the membership view's
`Members()`.

**Users**: v3rpc's `ClusterServer.MemberList` (`member.go:93`; its sketch cited "2e's spec"),
through it 1c's `cluster.MemberList` and `Client.Sync`. Snippet `etcdserverboot/members.go`
`ReqMemberListAfterAdd`.

**Proof sketch**: `isServer_names` gives the member's names `N`. With `lin`: the caller's
persistent update is registered at the current committed log (`readReg_register`), then
`LinearizableReadNotify.spec` at that log: an error is unsettled for a read (outcome 3: a read
fires nothing it cannot fire again); `nil` gives a committed log `l` the member applied
(`srvApplied`). `requireAuthInfo.spec` (its refusals: outcome 2, the update given back). The
view's `Members()` (2e's `RaftCluster.Members`: a fresh slice of the members, under its read lock,
the view at a point at or past the applied index, `srvReadAt`), a permutation of the history's
members at that point: `readReg_get` fires the update there (W0's `memberList` step: `σ' = σ`, the
members up to permutation when `lin`; any list otherwise, which W0's step allows).

**Changes**: verify round (A8-completeness F1): new here; the old tree's
`EtcdServer__MemberList.lean`, restated as a read of the client's model (`srvStep`'s
`.memberList lin`), shaped like `Range`.

**Margin**: the member list is not the cluster's in non-linearizable mode (W0's step allows any).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`MemberList(ctx, r)`**: the members, fired as the client's `memberList lin` read (outcome 1),
an auth refusal with the update given back (outcome 2), or an unsettled read error (outcome 3). -/
def EtcdServer.MemberList.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p tls : Principal) (r : Loc) (dq : DFrac)
    (lin : Bool) (lo : Nat) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
      Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗
      ClientV3.reqOwn r dq (.memberList lin) ∗ authLb γ lo ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep p tls (.memberList lin) σ σ' res lo⌝ ∗
           etcdState γ σ', COMM Q σ σ' res }> }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"MemberList")) (Val #ctx)) (Val #r))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); threadTok ∗
      ClientV3.reqOwn r dq (.memberList lin) ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ σ σ' ms, Q σ σ' (.ok (.memberList ms)) ∗
          Membership.membersOwn sl ms) ∨
       (∃ σ σ' e, Q σ σ' (.err e) ∗ srvErr err e ∗ srvErrShape err) ∨
       (srvUnfired err ∗ srvErrShape err) ∨
       (srvIndef err ∗ srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
