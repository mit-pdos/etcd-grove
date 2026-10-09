/-
Port of `election_proof/spec_Progress__BecomeProbe.v` (feb5c73d4).

Lean notes: Rocq's `Progress__BecomeProbeⁱᵐᵖˡ` is the Lean generated code
`tracker.Progress.BecomeProbe.impl`; `progress.t` is `Progress`, `own_Progress` is
`ownProgress`, `progress_become_probe` is `progressBecomeProbe`, `w64_min`/`w64_max` are
`w64Min`/`w64Max` (`Defs.lean`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `pr.BecomeProbe()` moves a `Progress` back to probing
(`tracker.Progress.BecomeProbe.impl`, Rocq new/code/go_etcd_io/raft/v3/tracker.v:249;
progress.go:130):

    if pr.State == StateSnapshot {
      pendingSnapshot := pr.PendingSnapshot
      pr.ResetState(StateProbe)
      pr.Next = max(pr.Match+1, pendingSnapshot+1)
    } else {
      pr.ResetState(StateProbe)
      pr.Next = pr.Match + 1
    }
    pr.sentCommit = min(pr.sentCommit, pr.Next-1)

One exit, no panic of its own; the one call is `ResetState`
(`spec_Progress__ResetState.v`, exact), which empties the `Inflights` and clears
`MsgAppFlowPaused` and `PendingSnapshot`. `Match` is untouched. The `+1`/`-1` are
`uint64` arithmetic and wrap silently in Go (and as `w64` `+`/`-` in Goose), so they
are stated that way rather than excluded by a premise: `ownProgress` bounds neither
`Match` nor `PendingSnapshot`. `min`/`max` are `w64Min`/`w64Max` (`Defs.lean`),
Goose's builtins verbatim. The new record is `progressBecomeProbe p` (`Defs.lean`). -/
abbrev tracker.Progress.BecomeProbe.spec : Prop :=
  ∀ (pr : Loc) (p : Progress),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"BecomeProbe"))
      (Val #()))
  {{ RET #(); ownProgress pr (progressBecomeProbe p) }}

end spec

end EtcdGrove
end Perennial
