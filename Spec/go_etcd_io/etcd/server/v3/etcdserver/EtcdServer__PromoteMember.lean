/-
`s.PromoteMember(ctx, id)` (`server.go`): the promotion of a learner, locally (`promoteMember`) or,
off the leader, forwarded to it. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20),
vocabulary `AuthGuard.lean`, `MemberContracts.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MemberContracts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
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

/-- **`s.PromoteMember(ctx, id)`**, any goroutine, at a context: `promoteMember(ctx, id)` (the admin
guard, `mayPromoteMember` and `configure`, the two callees contracts as `promoteMember.spec`'s, here
answering what the handler needs, `memChkAns`, `memCfgAns`); on its success that answer; on an error
other than `ErrNotLeader` the metric `learnerPromoteFailed` labelled with the error's message (valid
UTF-8: the guard's error is one of the auth package's variables, `authErrVarIs`, the contracts' errors
say so) and that error; on `ErrNotLeader`, the forwarding to the leader under a `ReqTimeout` child of
`ctx`: `waitLeader`, then `promoteMemberHTTP` to each of the leader's peer URLs, a names-only callee
taken as a contract (`promoteHTTPOk`: the leader re-checks the forwarded request, the caller's `Qfw`),
until a success, an error the leader refused the promotion with (`ErrLearnerNotReady`,
`ErrIDNotFound`, `ErrMemberNotLearner`), or the child is done (`ErrTimeout`, `ErrCanceled`). The
outcome: `configure`'s answer `memCfgAns Qin`; or an error with `Pin` kept (the guard's refusal,
`adminWhy` relative to the caller's lower bound `n` of the auth store's published index, `Pm` kept;
or, after a passing guard, the strict check's answer `memChkAns Qm`); or the leader's success, its
answer `Qfw` at `nil`; or an error of the forwarding (the leader's refusal, `waitLeader`'s, the child's
end). Every error is one `togRPCError` can take (`applyErrIs`). The context is an `isContext` (not `txnCtx`: the
forwarding's `context.WithTimeout` needs one). -/
abbrev EtcdServer.PromoteMember.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (tok : Option GoString) (id : w64) (Pin Pm : IProp GF)
    (Qm : GoInterface → IProp GF) (Qin Qfw : GoSlice → GoInterface → IProp GF) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvPeerRt s ∗
      srvAuthAt s E ∗ □ auth.authPubLbM E.authMode n ∗ context.isContext ctx cd ∗
      context.libCtxOk ctx ∗ □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗
      E.RD ∗ Pin ∗ Pm ∗ mayPromoteOk s id Pm (memChkAns Qm) ∗
      configureCcOk s E ctx (W32 0) id Pin (memChkAns Qm GoInterface.nil) (memCfgAns Qin) ∗
      promoteHTTPOk id Qfw }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"PromoteMember"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); E.RD ∗
      (memCfgAns Qin sl err ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ Pin ∗ applyErrIs err ∗
         ((adminWhy s E.authMode n tok err ∗ Pm) ∨
          ((∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo, adminRes E.authMode ai) ∗
            memChkAns Qm err))) ∨
       (⌜err = GoInterface.nil⌝ ∗ Qfw sl err) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
