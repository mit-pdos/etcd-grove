/-
`s.parseProposeCtxErr(err, start)` (`server.go`): the error of a proposal whose context is
done. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

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

/-- `s.parseProposeCtxErr(err, start)`, any goroutine, for a done context's error `err` (a typed
error, the value of `context.Canceled` or of `context.DeadlineExceeded`: Go's contract of
`Context.Err`, `context.ErrDone`): an error, not `nil`, one the gRPC layer can take
(`applyErrIs`): `ErrCanceled`, `ErrTimeoutDueToLeaderFail`, `ErrTimeoutDueToConnectionLost` or
`ErrTimeout` (the `default` branch, returning `err` itself, is not reached: `errors.Is` of an
error at itself is `true`, `errors.IsCtxErr`; 2026-10-12, unit 3a). It read-locks
`s.leadTimeMu`: the caller's reader slot. -/
abbrev EtcdServer.parseProposeCtxErr.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (err : GoInterface) (start : time.Time),
  context.isTypedErr err →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗
      (globalAddr context.Canceled ↦□ err ∨ globalAddr context.DeadlineExceeded ↦□ err) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"parseProposeCtxErr"))
      (Val #err)) (Val #start))
  {{ (e : GoInterface), RET #e; srvLeadTimeReader s ∗ ⌜e ≠ GoInterface.nil⌝ ∗ applyErrIs e }}

end spec

end EtcdGrove
end Perennial
