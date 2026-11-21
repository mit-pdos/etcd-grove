/-
`s.AddMember(ctx, memb)` (`server.go`): a membership operation, guarded by
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

/-- `s.AddMember(ctx, memb)`: the admin guard, then `json.Marshal(memb)` (no error, some bytes:
`Spec/encoding/json/MarshalMember.lean`), `mayAddMember(memb)` (the strict reconfiguration check)
and `configure(ctx, &cc)` with the add-node change of `memb.ID` (`ConfChangeAddLearnerNode` for a
learner) carrying those bytes; the two callees are names only, taken as contracts
(`MemberContracts.lean`): `mayAddOk` over the caller's `Pm` and the member's slices, answering
`Qm`; `configureCcOk` with the token `adminRes` of the request's auth info and the check's passing
`Qm nil`, over the caller's `Pin`, answering `Qin`. The member's slices are borrowed and given back.
The result is `configure`'s, or an error with `Pin` kept (the guard's error, `applyErrIs`, refused
for the admin class's reason `adminWhy` relative to the caller's lower bound `n` of the auth store's
published index, with `Pm` kept; or the check's `Qm err`). -/
abbrev EtcdServer.AddMember.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (tok : Option GoString) (memb : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
    (dp dc : DFrac) (ps cs : List GoString) (Pin Pm : IProp GF) (Qm : GoInterface → IProp GF)
    (Qin : GoSlice → GoInterface → IProp GF) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ □ auth.authPubLbM E.authMode n ∗ mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ E.RD ∗ Pin ∗ Pm ∗
      memberSlices memb dp dc ps cs ∗ mayAddOk s memb dp dc ps cs Pm Qm ∗
      configureCcOk s E ctx (addChangeType memb.RaftAttributes'.IsLearner') memb.ID' Pin
        (Qm GoInterface.nil) Qin }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AddMember"))
      (Val #(GoInterface.ok ctx))) (Val #memb))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); E.RD ∗
      memberSlices memb dp dc ps cs ∗
      (Qin sl err ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Pin ∗
        ((applyErrIs err ∗ adminWhy s E.authMode n tok err ∗ Pm) ∨ Qm err))) }}

end spec

end EtcdGrove
end Perennial
