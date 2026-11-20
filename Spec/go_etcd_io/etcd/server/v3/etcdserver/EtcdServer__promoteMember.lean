/-
`s.promoteMember(ctx, id)` (`server.go`): the local promotion of a learner, guarded by
`checkMembershipOperationPermission`. Lean-first (no Rocq counterpart); auth-mediation M2
(2026-11-20), vocabulary `AuthGuard.lean`, `MemberContracts.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MemberContracts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthWhy
public import Proof.context.LibKeys

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

/-- `s.promoteMember(ctx, id)`: the admin guard, then `mayPromoteMember(id)` (the learner's
readiness, `ErrNotLeader` off the leader, and the strict reconfiguration check), `json.Marshal` of
the promotion's context (`Spec/encoding/json/MarshalConfigChangeContext.lean`: no error, some bytes)
and `configure(ctx, &cc)` with the add-node change (`ConfChangeAddNode`, 0) of `id` carrying those
bytes; the two callees are names only, taken as contracts (`MemberContracts.lean`): `mayPromoteOk`
over the caller's `Pm`, answering `Qm`; `configureCcOk` with the token `adminRes` of the request's
auth info and the check's passing `Qm nil`, over the caller's `Pin`, answering `Qin`. The result is
`configure`'s, or an error with `Pin` kept (the guard's error, `applyErrIs` and one of the auth
package's error variables, `authErrVarIs` (auth-mediation M2, 2026-11-20), refused for the admin
class's reason `adminWhy` relative to the caller's lower bound `n` of the auth store's published
index, with `Pm` kept; or the check's `Qm err`, after a passing guard: the token for some auth
info). -/
abbrev EtcdServer.promoteMember.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (tok : Option GoString) (id : w64) (Pin Pm : IProp GF) (Qm : GoInterface → IProp GF)
    (Qin : GoSlice → GoInterface → IProp GF) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ □ auth.authPubLbM E.authMode n ∗ mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ E.RD ∗ Pin ∗ Pm ∗
      mayPromoteOk s id Pm Qm ∗ configureCcOk s E ctx (W32 0) id Pin (Qm GoInterface.nil) Qin }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"promoteMember"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); E.RD ∗
      (Qin sl err ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Pin ∗
        ((applyErrIs err ∗ authErrVarIs err ∗ adminWhy s E.authMode n tok err ∗ Pm) ∨
         ((∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo, adminRes E.authMode ai) ∗
          Qm err)))) }}

end spec

end EtcdGrove
end Perennial
