/-
Lean-first (no Rocq counterpart): `traceNodeEvent` (`state_trace.go`, translated under the `goose`
tag since 2026-11-08, `notes/trace-validation-hooks.md`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap
public import Proof.go_etcd_io.raft.v3.RaftReadLend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `traceNodeEvent(evt, r)`: `traceEvent(evt, r, nil, nil)`, the node event `evt` of `r`'s state.

One spec for both modes (Q8 stage 1, slice 2, 2026-11-09), by the node's mode `s.gh.tr`: the gate
`trOwn s.gh.tr` lends raft's state only when traced (an untraced caller, holding the struct open or
not, gives nothing), and `TraceFire s.gh.tr tl (NodeEvOf evt id s c) Q` is a nil logger and `Q`
untraced, the logger's contract and the caller's update for any `NodeEvOf` event traced. Its traced
instance is the Draft's `traceNodeEvent.tracedSpec` (`TracedHooks.lean`). `evt.String()` panics past
the event names (review round 1's F1), hence the premise. Until slice 2: `⌜TraceLoggerOk tl⌝`,
giving `True` (increment 1, `notes/trace-validation-hooks.md`). -/
abbrev traceNodeEvent.spec : Prop :=
  ∀ (evt : w64) (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q P : IProp GF),
  uint.nat evt < evtNames.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      -- (2026-11-12, trace-check step 5; until then the whole struct, `ownRaftPhysCV c c.voters r id s`)
      -- raft's state lent read-only out of `P` (`newRaft`'s `traceInitState` runs before the struct is
      -- `ownRaftPhysCV`)
      trOwn s.gh.tr iprop(P ∗ RaftReadLend P c r id s) ∗ TraceFire s.gh.tr tl (NodeEvOf evt id s c) Q }}
    (App (App (Val #(functions traceNodeEvent [])) (Val #evt)) (Val #r))
  {{ RET #(); trOwn s.gh.tr P ∗ Q }}

end spec

end EtcdGrove
end Perennial
