/-
`s.MemberList(ctx, r)` (`server.go`): the member list, guarded by `requireAuthInfo` (after the
linearizable read's notify when the request asks for one). Lean-first (no Rocq counterpart); the
auth plan's A2 (2026-10-23), vocabulary `AuthGuard.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.MemberList(ctx, r)`: with `r.Linearizable`, the read loop's `LinearizableReadNotify`
(`isReadNotify`, the reader's view; its resources as `EtcdServer.LinearizableReadNotify.spec`:
the committed index `c` the caller knew of, the reader slot `srvReadReader`, the saved predicate
`g`); then the authenticated-user guard; then the cluster's `Members()`. On `nil`: the members
(`membersAt`), the guard's token `authedRes`, and with `r.Linearizable` the read index
(`readIndexOk`, `readServed`). -/
abbrev EtcdServer.MemberList.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (lin : Bool) (dq : DFrac) (c : w64)
    (g : GName) (Q : List EntryModel → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ mvcc.txnCtx ctx cd ∗ E.RD ∗
      structFieldRef etcdserverpb.MemberListRequest go!"Linearizable" r ↦{dq} lin ∗
      srvReadReader s γr ∗ committedAtLeast γr c ∗ savedPredOwn g DFrac.discard Q ∗
      kvDep γr.kv Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"MemberList"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); E.RD ∗
      structFieldRef etcdserverpb.MemberListRequest go!"Linearizable" r ↦{dq} lin ∗
      srvReadReader s γr ∗ applyErrIs err ∗
      (∀ _ : err = GoInterface.nil, (∃ ms : List Loc, membership.membersAt sl ms) ∗
        (∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo, authedRes E.authMode ai) ∗
        (∀ _ : lin = true, readIndexOk γr c ∗ readServed γr c g)) }}

end spec

end EtcdGrove
end Perennial
