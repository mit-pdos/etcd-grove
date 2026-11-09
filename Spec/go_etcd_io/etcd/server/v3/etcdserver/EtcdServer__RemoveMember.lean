/-
## `(*EtcdServer).RemoveMember(ctx, id)` (`server.go:1465-1481`): translated

**Users.** 2a's `ClusterServer.MemberRemove`; the integration framework's member removal.

**Proof sketch.** `checkMembershipOperationPermission` (the admin check: a refusal),
`mayRemoveMember` (names only: `StrictReconfigCheck`'s quorum check, a refusal), `configure` of a
`RemoveNode` change: the `memberRemove` step at its commit. (A removed member's own server stops
itself: 2d's `applyConfChange`; its gate is the program's to drain, `HardStop.spec`.)

**Changes** (from `specs-ref`'s `EtcdServer__RemoveMember.lean`): over W0's step. **Margin.** As
`AddMember`.
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

/-- **Removes member `id`**, as the cluster's `memberRemove` step. -/
def EtcdServer.RemoveMember.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (who : Principal)
    (id : w64) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗ reqPrin ctx who ∗ Context.ctxOk ctx ∗ threadTok ∗
      AU <{{ ∃∃ (σ : State), etcdState γ σ }}> @ ⊤ \ ↑etcdN, ∅
        <{{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep who (.memberRemove (uint.nat id)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }}> }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"RemoveMember")) (Val #ctx)) (Val #id))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); srvGate s q ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ ((∃ l : List Member, ⌜respMembers res = some l ∧ err = GoInterface.nil⌝ ∗
          ∃ ms, Membership.membersOwn sl ms ∗ ⌜ms.Perm l⌝) ∨
       (∃ e, ⌜res = .err e⌝ ∗ ⌜srvErrOf err e⌝))) ∨
       (⌜srvUnfired err⌝ ∗ AU <{{ ∃∃ (σ : State), etcdState γ σ }}> @ ⊤ \ ↑etcdN, ∅
        <{{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep who (.memberRemove (uint.nat id)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }}>) ∨
       ⌜srvIndef err⌝) }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
