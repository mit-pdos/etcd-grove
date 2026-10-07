/-
Port of `election_proof/spec_Progress__ResetState.v` (feb5c73d4).

Lean notes: `prstate.t` is `PRState`, `prstate_w64` is `prstateW64`,
`progress_reset_state` is `progressResetState` (`Defs.lean`).
-/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `pr.ResetState(st)` resets the `Progress` to state `st` and empties its
`Inflights` (whence the `Inflights.reset` postulate):

    pr.MsgAppFlowPaused = false
    pr.PendingSnapshot = 0
    pr.State = state
    pr.Inflights.reset()

Stated on `ownProgress` at the exact new record, `progressResetState p st`
(`Defs.lean`). The argument is a `PRState` passed as its `StateType` (`prstateW64`),
so no other value can be passed -- what the premise `ProgressStateOk st` said until
2026-10-02. (Until 2026-09-23 it was stated on the raw field points-tos.) -/
abbrev tracker.Progress.ResetState.spec : Prop :=
  ∀ (pr : Loc) (p : Progress) (st : PRState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"ResetState"))
      (Val #(prstateW64 st)))
  {{ RET #(); ownProgress pr (progressResetState p st) }}

end spec

end EtcdGrove
end Perennial
