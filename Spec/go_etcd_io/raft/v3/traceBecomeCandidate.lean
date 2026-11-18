/-
Port of election_proof/spec_traceBecomeCandidate.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap

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

/-- `traceBecomeCandidate(r)`: the node event `BecomeCandidate` of `r`'s state, through `traceNodeEvent`.

One spec for both modes (Q8 stage 1, slice 2, 2026-11-09; `traceNodeEvent.spec`'s form): untraced
(`s.gh.tr = none`) the gate `trOwn` is `emp` and `TraceFire` a nil logger and `Q`; traced, raft's state
is lent through the gate and the caller's update fires with a `NodeEvOf` event. Its traced instance is
the Draft's `traceBecomeCandidate.tracedSpec` (`TracedHooks.lean`). Until slice 2: `⌜TraceLoggerOk tl⌝`, giving
`True` (increment 1, `notes/trace-validation-hooks.md`). -/
abbrev traceBecomeCandidate.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      trOwn s.gh.tr (ownRaftPhysCV c c.voters r id s) ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 1) id s c) Q }}
    (App (Val #(functions traceBecomeCandidate [])) (Val #r))
  {{ RET #(); trOwn s.gh.tr (ownRaftPhysCV c c.voters r id s) ∗ Q }}

end spec

end EtcdGrove
end Perennial
