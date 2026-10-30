/-
`s.AuthEnable(ctx, r)` (`v3_server.go`): `raftRequest` on `&pb.InternalRaftRequest{AuthEnable: r}`. Lean-first
(no Rocq counterpart); the auth plan's A3, the API layer (2026-10-24), vocabulary `AuthEntry.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthEntry
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminOn

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

/-- **`s.AuthEnable(ctx, r)`** for a non-nil request `r`: `raftRequest` on the request
`irrAuthEnable` (`&pb.InternalRaftRequest{AuthEnable: r}`), taken as the contract `authRaftOk` for the
response type `*pb.AuthEnableResponse` (`AuthEntry.lean`: the proposal path is proved for the KV requests
only, `reqPropOk`), over the caller's `P` answering `Q`; the outcome `authEntryOut`: the applied
response (typed) with `Q resp nil`, or `nil` and the error with `Q null err`. The admin check of
this request is the apply layer's (`apply.adminPass`, for the header's principal). -/
abbrev EtcdServer.AuthEnable.spec : Prop :=
  ∀ (s : Loc) (ctx : GoInterfaceOk) (r : Loc) (P : IProp GF)
    (Q : Loc → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜r ≠ null⌝ ∗ P ∗
      authRaftOk s ctx (irrAuthEnable) etcdserverpb.AuthEnableResponse.ty P Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AuthEnable"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); applyErrIs err ∗ authEntryOut Q resp err }}

/-- **`s.AuthEnable(ctx, r)` with auth on** (the auth plan's E3w, 2026-10-27; `AdminOn.lean`): `spec`
with its contract `raftRequest.specM true`'s (`authRaftOk_on`), the request admitted (`adminPropOk`);
the outcome `authEntryOut` of `adminOutOn`: on success, the request applied at the committed prefix
`L` before its entry (`appliedOkM true`), the auth state after it published (`pubAfterM true`) and
its step determinate there (`adminQh`), with (5b) the result `Q` of its client's update of the
auth history (`histAu`) if its entry is recorded; else the apply thread's error, or the request
perhaps proposed. -/
abbrev EtcdServer.AuthEnable.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF))
    (Q : List auth.AuthState → IProp GF) (r : Loc) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜r ≠ null⌝ ∗
      adminPreOn s E ρ ctx cd F
        (adminHistAu s E ρ ctx irrAuthEnable Q) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AuthEnable"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); applyErrIs err ∗
      authEntryOut (adminOutOn s E ρ ctx irrAuthEnable F (adminQh ρ.kv irrAuthEnable Q)
        etcdserverpb.AuthEnableResponse.ty) resp err }}

end spec

end EtcdGrove
end Perennial
