/-
Port of election_proof/spec_traceInitState.v (feb5c73d4).
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

/-- `traceInitState(r)`: returns at once on a nil logger (its own check); otherwise the node event
`InitState` of `r`'s state, through `traceNodeEvent`.

One spec for both modes (Q8 stage 1, slice 2, 2026-11-09), by the caller's mode `tr` (`newRaft` calls
it before raft's predicate holds, so it has no node state yet: the Draft's S5, open), in
`traceEvent.spec`'s lending form: under the gate `trOwn tr`, raft's state at some configuration, of
mode `tr`, with every `InitState` event of it allowed by `E`, lent back to `R`; the event builder's
gate `TraceFire tr tl E Q`. Its traced instance is the Draft's `traceInitState.tracedSpec`
(`TracedHooks.lean`). Until slice 2: `⌜TraceLoggerOk tl⌝`, giving `True`. -/
abbrev traceInitState.spec : Prop :=
  ∀ (r : Loc) (tl : GoInterface) (tr : Option GName) (E : TraceEv → Prop) (Q R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      trOwn tr iprop(∃ (c : CfgM) (id : w64) (s : NState), ownRaftPhysCV c c.voters r id s ∗
        ⌜s.gh.tr = tr ∧ ∀ e, NodeEvOf (W64 0) id s c e → E e⌝ ∗
        (ownRaftPhysCV c c.voters r id s -∗ R)) ∗
      TraceFire tr tl E Q }}
    (App (Val #(functions traceInitState [])) (Val #r))
  {{ RET #(); trOwn tr R ∗ Q }}

end spec

end EtcdGrove
end Perennial
