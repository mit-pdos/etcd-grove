/-
**The NOSPACE alarm's proposal** (`applyEntryNormal`'s goroutine: `s.raftRequest(s.ctx,
&pb.InternalRaftRequest{Alarm: a})`): a trust-boundary contract, the request path's unit 4c
(2026-10-13). Lean-first.

When the applier answers `ErrNoSpace` and no alarm is raised yet, the apply thread `GoAttach`es a
goroutine that proposes the NOSPACE alarm through raft and then hands the entry's result to its
waiter (`s.w.Trigger(id, ar)`). The goroutine is verified (`EtcdServer.applyEntryNormal`'s proof:
its `GoAttach`, the alarm request built, the trigger) but for the proposal itself: `raftRequest`
is verified for the request path's proposers (`EtcdServer.raftRequest.spec`), which hold an id
credit of the request path's budget (`idCred`), a reader slot of `leadTimeMu` and the proposer's
view `isServerReq`; the apply thread's goroutine holds none of them (it is not a request
goroutine, and an unbounded number of them may run). This contract states that the proposal, by
such a goroutine of a server the apply thread sees (`isServer`), at the server's context, of a
fresh request it owns, returns. It was the trust boundary before too: `GoAttach` was an axiom
(`{True} GoAttach(f) {True}` for every `f`, the alarm goroutine unverified).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The NOSPACE alarm's proposal returns** (see the file header). -/
abbrev EtcdServer.raftRequestAlarm.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (c : GoInterface) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗ (∃ v : etcdserverpb.InternalRaftRequest, p ↦ v) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest")) (Val #c))
      (Val #p))
  {{ (resp err : GoInterface), RET (PairV #resp #err); True }}

axiom EtcdServer.raftRequestAlarm.wp_proof : EtcdServer.raftRequestAlarm.spec (GF := GF) (hG := hG)

end spec

end EtcdGrove
end Perennial
