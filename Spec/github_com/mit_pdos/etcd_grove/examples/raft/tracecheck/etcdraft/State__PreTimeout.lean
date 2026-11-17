/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.PreTimeout(i)`: the action
`PreTimeout(i)`, with `PreVote` off.
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

/-- `s.PreTimeout(i)`, of a state with `PreVote` off (`NewTrace`'s: the workload's raft runs
without pre-vote, and every action keeps the flag): `preTimeout i`'s successor, `nil` (the action
is not enabled). Pre-vote is outside what the checker's proof needs (`notes/trace-validation-plan.md`,
layer C), so the action is specified only where the flag is off. -/
abbrev State.PreTimeout.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ ⌜uint.nat i ∈ st.server ∧ st.preVote = false⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"PreTimeout")) (Val #i))
  {{ (q : Loc), RET #q;
      match st.preTimeout (uint.nat i) with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
