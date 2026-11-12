/-
Lean-first (no Rocq counterpart): `makeTracingState` (`state_trace.go`), a traced event's state
(Q8 stage 1, slice 2, 2026-11-09).
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

/-- `makeTracingState(r)`: the hard state's term, vote (in decimal) and commit index, read through
`r.hardState()` from raft's state, which it gives back. (2026-11-12, trace-check step 4) On the
fields `hardState` reads (`ownRaftCore`), as `traceEvent`'s read view lends them; until then on
`ownRaftPhysCV c c.voters`. -/
abbrev makeTracingState.spec : Prop :=
  ∀ (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftCore r id s }}
    (App (Val #(functions makeTracingState [])) (Val #r))
  {{ (ts : TracingState), RET #ts; ownRaftCore r id s ∗
      ⌜ts.Term' = s.term ∧ ts.Vote' = decStr s.vote ∧ ts.Commit' = s.logst.committed⌝ }}

end spec

end EtcdGrove
end Perennial
