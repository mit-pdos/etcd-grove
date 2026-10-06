/-
Port of `election_proof/spec_Progress__ResetState.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- `pr.ResetState(st)` resets the `Progress` to state `st` and empties its `Inflights`
(whence the `Inflights.reset` postulate). Stated on `ownProgress` at the exact new
values, so a caller that has to keep stepping field reads afterwards opens the predicate
it gets back. (Until 2026-09-23 it was stated on the raw field points-tos, for exactly
that reason -- the reason is answered by the exact index, not by a second shape.)
`ProgressStateOk st` is what keeps `ownProgress`'s own invariant; both callers pass a
literal state. -/
abbrev tracker.Progress.ResetState.spec : Prop :=
  ∀ (pr : Loc) (pv : tracker.Progress) (iv : tracker.Inflights) (st : tracker.StateType),
  ProgressStateOk st →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownProgress pr pv iv }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"ResetState"))
      (Val #st))
  {{ RET #();
      ownProgress pr
        { pv with MsgAppFlowPaused' := false, PendingSnapshot' := W64 0, State' := st }
        { iv with start' := W64 0, count' := W64 0, bytes' := W64 0 } }}

end spec

end EtcdGrove
end Perennial
