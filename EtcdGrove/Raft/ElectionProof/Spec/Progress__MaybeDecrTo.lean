/- Port of election_proof/spec_Progress__MaybeDecrTo.v (feb5c73d4). -/
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

/-- `pr.MaybeDecrTo(rejected, matchHint)` reacts to a rejected `MsgApp`
(`tracker.Progress.MaybeDecrTo.impl`, `Perennial/Code/go_etcd_io/raft/v3/tracker.lean`;
progress.go:226):

    if pr.State == StateReplicate {
      if rejected <= pr.Match { return false }            // exit 1: stale
      pr.Next = pr.Match + 1
      pr.sentCommit = min(pr.sentCommit, pr.Next-1)
      return true                                          // exit 2
    }
    if pr.Next-1 != rejected { return false }              // exit 3: stale
    pr.Next = max(min(rejected, matchHint+1), pr.Match+1)
    pr.sentCommit = min(pr.sentCommit, pr.Next-1)
    pr.MsgAppFlowPaused = false
    return true                                            // exit 4

Four exits, no panic, no call (`min`/`max` are builtins). `Match`, `State` and the
`Inflights` are never written. Every `+1`/`-1` is `uint64` arithmetic, which Go wraps
silently and Goose renders as `w64` addition/subtraction -- `ownProgress` bounds neither
`Next` nor `Match`, so `pr.Next-1` at `Next = 0` and `pr.Match+1` at `Match = 2^64-1`
really do wrap. The postcondition therefore states the body's arithmetic verbatim
rather than excluding the wrap by a premise; `w64Min`/`w64Max` (`Defs.lean`) are
Goose's `min`/`max`. `progressMaybeDecrTo p rejected matchHint` (`Defs.lean`) is the
pair (result, new record), the four exits in order. -/
abbrev tracker.Progress.MaybeDecrTo.spec : Prop :=
  ∀ (pr : Loc) (p : Progress) (rejected matchHint : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr p }}
    (App (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"MaybeDecrTo"))
      (Val #rejected)) (Val #matchHint))
  {{ RET #((progressMaybeDecrTo p rejected matchHint).1);
      ownProgress pr (progressMaybeDecrTo p rejected matchHint).2 }}

end spec

end EtcdGrove
end Perennial
