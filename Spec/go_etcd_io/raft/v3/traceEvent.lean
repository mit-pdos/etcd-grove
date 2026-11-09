/-
Lean-first (no Rocq counterpart): `traceEvent` (`state_trace.go`, translated under the `goose`
tag since 2026-11-08, `notes/trace-validation-hooks.md`).
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

/-- `traceEvent(evt, r, m, prop)`: reads `r.traceLogger` and returns when it is nil; otherwise
builds the event from `r`'s state and calls the logger's `TraceEvent`.

One spec for both modes (Q8 stage 1, slice 2, 2026-11-09), by the caller's mode `tr`: the logger's
gate `TraceFire tr tl E Q` (untraced: a nil logger and `Q`, `TraceLoggerOk`; traced: the logger's
contract and the update for any event `E` allows, giving `Q`), and under the gate `trOwn tr` what
only the traced branch reads: raft's state at some configuration, lent (given back through the
caller's wand, to `R`), with every event of it the builder may log allowed by `E` (`NodeEvOf`: the
state's term, vote, commit, role, last index, each configuration half's voters in some order). The
traced case covers node events so far (`m` and `prop` nil, `traceNodeEvent`'s call); a message's and a
configuration change's events are to come (a message's type name is the plan's Q9). Until slice 2
the spec was the untraced case alone (`⌜TraceLoggerOk tl⌝`, giving `True`). -/
abbrev traceEvent.spec : Prop :=
  ∀ (evt : w64) (r m : Loc) (prop : GoMap) (tl : GoInterface) (tr : Option GName)
    (E : TraceEv → Prop) (Q R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      trOwn tr iprop(∃ (c : CfgM) (id : w64) (s : NState), ownRaftPhysCV c c.voters r id s ∗
        ⌜m = null ∧ prop = null ∧ uint.nat evt < evtNames.length ∧
          ∀ e, NodeEvOf evt id s c e → E e⌝ ∗
        (ownRaftPhysCV c c.voters r id s -∗ R)) ∗
      TraceFire tr tl E Q }}
    (App (App (App (App (Val #(functions traceEvent [])) (Val #evt)) (Val #r)) (Val #m)) (Val #prop))
  {{ RET #(); trOwn tr R ∗ Q }}

end spec

end EtcdGrove
end Perennial
