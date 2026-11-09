/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.receive(ts)`, `TraceNextReceiveActions`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `t.receive(ts)`, at a position of the trace, of a state whose bags the Go's `Bag` handles
(`Bag.Ok`) and whose messages each meet `State.Receive`'s premises (none a pre-vote one or a snapshot,
`prevLogIndex` in `[0, 2^62 - 1)`, entries and the destination's log far from overflow): `tr.receive
ts`'s successors (it never fails there), fresh. -/
abbrev Trace.receive.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ ts.l ≤ tr.len ∧ ts.s.pendingMessages.Ok ∧ ts.s.messages.Ok ∧
        ∀ m ∈ ts.s.messages.domain, m.type ≠ .preVoteRequest ∧ m.type ≠ .preVoteResponse ∧
          m.subtype ≠ "snapshot" ∧ 0 ≤ m.prevLogIndex ∧ m.prevLogIndex + 1 < 2 ^ 62 ∧
          m.entries.length < 2 ^ 62 ∧ (m.dest ∈ ts.s.server → (ts.s.s m.dest).log.length < 2 ^ 62)⌝ }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"receive")) (Val #g))
  {{ (out : GoSlice), RET #out;
      match tr.receive ts with
      | .ok tss => tstatesOut out tss
      | .error _ => False }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
