/-
Port of `election_proof/spec_Progress__IsPaused.v`.

Lean notes: Rocq's `progress_paused` is `progressPaused`, with `if decide (…)` as a
plain `if`.
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

/-- `pr.IsPaused()` -- "should the leader hold off sending log entries to this peer".
The body (`tracker.Progress.IsPaused.impl`, `Perennial/Code/go_etcd_io/raft/v3/tracker.lean`)
switches on `pr.State`:

    StateProbe, StateReplicate -> pr.MsgAppFlowPaused
    StateSnapshot              -> true
    anything else              -> panic("unexpected state")

The fourth arm is why `ownProgress` carries `ProgressStateOk` (`InvTracker.lean`):
`bcastAppend` reaches `IsPaused` on every peer, so the panic has to be ruled out by an
invariant rather than by inspection.

Stated at a fixed `Progress` value (`ownProgress pr pv iv`) because the answer *is* a
function of that value, and `maybeSendAppend` needs to know which branch it took: a
`false` answer tells it `State ≠ StateSnapshot`, which is what makes the later
`SentEntries` call legal (that one panics in `StateSnapshot`). -/
def progressPaused (pv : tracker.Progress) : Bool :=
  if pv.State' = W64 2 then true
  else pv.MsgAppFlowPaused'

abbrev tracker.Progress.IsPaused.spec : Prop :=
  ∀ (pr : Loc) (pv : tracker.Progress) (iv : tracker.Inflights),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr pv iv }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"IsPaused")) (Val #()))
  {{ RET #(progressPaused pv); ownProgress pr pv iv }}

end spec

end EtcdGrove
end Perennial
