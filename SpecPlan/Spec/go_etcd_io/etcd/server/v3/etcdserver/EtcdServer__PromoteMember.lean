/-
## `(*EtcdServer).PromoteMember(ctx, id)` (`server.go:1483-1527`): names only

**Users.** 2a's `ClusterServer.MemberPromote`.

**Why it is true.** On a leader, `promoteMember` (`mayPromoteMember`: the learner caught up, a
refusal otherwise; then `configure` of an `AddNode` change with `IsPromote`); on a follower, the
request forwarded to the leader over HTTP (`promoteMemberHTTP`: the leader's answer, or an indefinite
error); the `memberPromote` step at the commit.

**Changes**: new. **Margin.** As `AddMember`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

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

/-- **Promotes learner `id`**, as the cluster's `memberPromote` step. -/
def EtcdServer.PromoteMember.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (pr tls : Principal) (lo : Nat)
    (id : w64) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗ reqPrin ctx pr tls ∗ authLb γ lo ∗ Context.ctxOk ctx ∗ threadTok ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep pr tls (.memberPromote (uint.nat id)) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"PromoteMember")) (Val #ctx)) (Val #id))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); srvGate s q ∗ threadTok ∗
      ((∃ σ σ' res, ⌜srvFiredAns res⌝ ∗ Q σ σ' res ∗ ((∃ l : List Member, ⌜respMembers res = some l ∧ err = GoInterface.nil⌝ ∗
          ∃ ms, Membership.membersOwn sl ms ∗ ⌜ms.Perm l⌝) ∨
       (∃ e, ⌜res = .err e⌝ ∗ srvErr err e))) ∨
       (srvUnfired err ∗ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep pr tls (.memberPromote (uint.nat id)) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }>) ∨
       srvIndef err) }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
