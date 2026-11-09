/-
## `(*EtcdServer).UpdateMember(ctx, memb)` (`server.go:1676-1691`): names only

**Users.** 2a's `ClusterServer.MemberUpdate`.

**Why it is true.** `json.Marshal`, the admin check, `configure` of an `UpdateNode` change: the
`memberUpdate` step at its commit (`ccResult`: `memberNotFound`, `peerURLExist`, or the update).
Takes the URL set's single-use right (as `AddMember`).

**Changes**: new. **Margin.** As `AddMember`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

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

/-- **Changes member `memb.ID`'s peer URLs** to `urls`, as the cluster's `memberUpdate` step. -/
def EtcdServer.UpdateMember.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (pr tls : Principal) (lo : Nat)
    (memb : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member) (urls : List GoString) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗ reqPrin ctx pr tls ∗ authLb γ lo ∗ Context.ctxOk ctx ∗ threadTok ∗
      memb.RaftAttributes'.PeerURLs' ↦*□ urls ∗ urlsRight γ urls ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep pr tls (.memberUpdate (uint.nat memb.ID') urls) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"UpdateMember")) (Val #ctx)) (Val #memb))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); srvGate s q ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ ((∃ l : List Member, ⌜respMembers res = some l ∧ err = GoInterface.nil⌝ ∗
          ∃ ms, Membership.membersOwn sl ms ∗ ⌜ms.Perm l⌝) ∨
       (∃ e, ⌜res = .err e⌝ ∗ ⌜srvErrOf err e⌝))) ∨
       (⌜srvUnfired err⌝ ∗ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep pr tls (.memberUpdate (uint.nat memb.ID') urls) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }>) ∨
       ⌜srvIndef err⌝) }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
