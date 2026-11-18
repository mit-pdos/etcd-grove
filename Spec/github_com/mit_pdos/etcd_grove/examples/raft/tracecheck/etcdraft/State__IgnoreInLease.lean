/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.IgnoreInLease(m)`: the action
`IgnoreInLease(m)`, with `CheckQuorum` off.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Own

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

/-- `s.IgnoreInLease(m)`, of a state with `CheckQuorum` off (`NewTrace`'s: the workload's raft runs
without check-quorum, and every action keeps the flag): `ignoreInLease m`'s successor, `nil` (the
action is not enabled). Check-quorum is outside what the checker's proof needs
(`notes/trace-validation-plan.md`, layer C), so the action is specified only where the flag is off. -/
abbrev State.IgnoreInLease.spec : Prop :=
  ∀ (p : Loc) (st : State) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ msgRO q m ∗ ⌜st.checkQuorum = false⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"IgnoreInLease")) (Val #q))
  {{ (r : Loc), RET #r;
      match st.ignoreInLease m with
      | none => ⌜r = null⌝
      | some st' => stateRO r st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
