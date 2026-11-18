/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.requestVoteIfLogged(ts, i, j)`,
`RequestVoteIfLogged(i, j)`.
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

/-- `t.requestVoteIfLogged(ts, i, j)`, of a server `i` of a state whose pending bag the Go's `Bag`
handles (`RequestVote`'s premises) and whose `PreVote` is off (`RequestPreVote`'s: pre-vote is outside
what the checker's proof needs, the trace's `NewTrace` sets the flag off and every action keeps it):
`tr.requestVoteIfLogged ts i j`'s successors. -/
abbrev Trace.requestVoteIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server ∧ ts.s.pendingMessages.Ok ∧ ts.s.preVote = false⌝ }}
    (App (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"requestVoteIfLogged")) (Val #g)) (Val #i)) (Val #j))
  {{ (out : GoSlice), RET #out; statesOut out (tr.requestVoteIfLogged ts (uint.nat i) (uint.nat j)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
