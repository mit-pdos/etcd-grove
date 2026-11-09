/-
## `(*EtcdServer).AddMember(ctx, memb)` (`server.go:1406-1432`): names only (it calls `json.Marshal`)

**Users.** 2a's `ClusterServer.MemberAdd` (`v3rpc/member.go`, with a member from
`membership.NewMember`/`NewMemberAsLearner`); `ReqJoin`.

**Why it is true** (trusted; each path of the code): `checkMembershipOperationPermission` (the
admin check at the member's auth state: a refusal), `json.Marshal` of the member (cannot fail for
this struct), `mayAddMember` (`StrictReconfigCheck`: a refusal when not healthy), then `configure`
(`EtcdServer.configure.spec`): an `AddNode`/`AddLearnerNode` conf change proposed once, its update
fired at the entry's commit by 2d's apply (`applyConfChange`: `ValidateConfigurationChange`'s
`ccResult` decides the answer: `peerURLExist`, `memberExist`, `tooManyLearners`, ... or the add),
the answer the members after it (`Members()` at the apply).

**`urlsRight`** (round 1, provability F4): giving a member a URL set takes its single-use right, so
no member is added (or updated) onto URLs a pending joiner holds. A workload premise on the
program's `MemberAdd` calls, carried to 1c's `Cluster.MemberAdd` and 2a's handler
(`req/…client_v3.md`, `req/…api_v3rpc.md`, "from 2e, round 1").

**Changes**: new (2a's item 7; round 1, completeness F4). **Margin.** The answer's member list is
any permutation.

Changes: verify-round (A8-completeness F2, second tier): a refusal (fired with no change, or not fired) gives `urlsRight` back, so a refused add can be retried; the right at the parsed URLs' strings needs W0's normalization law (requested of client-core).
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

/-- **Adds a member** with the peer URLs `urls` (a learner if `learner`), as the cluster's `memberAdd` step. -/
def EtcdServer.AddMember.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (pr tls : Principal) (lo : Nat)
    (memb : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member) (urls : List GoString)
    (learner : Bool) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗ reqPrin ctx pr tls ∗ authLb γ lo ∗ Context.ctxOk ctx ∗ threadTok ∗
      memb.RaftAttributes'.PeerURLs' ↦*□ urls ∗ ⌜memb.RaftAttributes'.IsLearner' = learner⌝ ∗
      urlsRight γ urls ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep pr tls (.memberAdd urls learner) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"AddMember")) (Val #ctx)) (Val #memb))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); srvGate s q ∗ threadTok ∗
      ((∃ σ σ' res, ⌜srvFiredAns res⌝ ∗ Q σ σ' res ∗ ((∃ l : List Member, ⌜respMembers res = some l ∧ err = GoInterface.nil⌝ ∗
          ∃ ms, Membership.membersOwn sl ms ∗ ⌜ms.Perm l⌝) ∨
       (∃ e, ⌜res = .err e⌝ ∗ srvErr err e ∗ urlsRight γ urls))) ∨
       (srvUnfired err ∗ urlsRight γ urls ∗ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep pr tls (.memberAdd urls learner) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }>) ∨
       srvIndef err) }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
