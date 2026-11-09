/-
## `(*EtcdServer).configure(ctx, cc)` (`server.go:1779-1821`): names only (the member operations' tail)

**Users.** `AddMember`, `RemoveMember`, `UpdateMember`, `promoteMember`.

**Why it is true.** A fresh request id (`reqIDGen.Next`), a waiter registered (2c's `pkg/wait`),
`ProposeConfChange` (raft's: the caller's update deposited with the proposal: 2d's `histPropose`),
then the waiter's `confChangeResponse` (2d's `applyConfChange`, after raft advanced past the entry)
with the members and the validation's error; or the context's end (`parseProposeCtxErr`:
indefinite), or the stop (`ErrStopped`: indefinite).

**Changes**: new. **Margin.** As `AddMember`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import Spec.go_etcd_io.raft.v3.Api

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

/-- **Proposes the conf change `cc` for the request `rq`** and waits for its answer. -/
def EtcdServer.configure.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (pr tls : Principal) (lo : Nat) (pc : Loc)
    (dq : DFrac) (cc : Raft.ConfChangeV1) (rq : Req) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗ reqPrin ctx pr tls ∗ authLb γ lo ∗ Context.ctxOk ctx ∗ threadTok ∗
      Raft.confChangePts (interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfChange.ty) #pc)
        dq (.v1 cc) ∗ ⌜Membership.ccPanicFree cc⌝ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep pr tls (rq) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"configure")) (Val #ctx)) (Val #pc))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); srvGate s q ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ ((∃ l : List Member, ⌜respMembers res = some l ∧ err = GoInterface.nil⌝ ∗
          ∃ ms, Membership.membersOwn sl ms ∗ ⌜ms.Perm l⌝) ∨
       (∃ e, ⌜res = .err e⌝ ∗ ⌜srvErrOf err e⌝))) ∨
       (⌜srvUnfired err⌝ ∗ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep pr tls (rq) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }>) ∨
       ⌜srvIndef err⌝) }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
