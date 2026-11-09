/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.BecomeLeader(i)`: the action `BecomeLeader(i)`.
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

/-- `s.BecomeLeader(i)`, of a server `i` of the state (its granted votes fewer than `2^62`,
`IsQuorum`'s premise): `becomeLeader i`'s successor, a new read-only state, or `nil` where it is not
enabled. -/
abbrev State.BecomeLeader.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ ⌜uint.nat i ∈ st.server ∧ (st.s (uint.nat i)).votesGranted.length < 2 ^ 62⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"BecomeLeader")) (Val #i))
  {{ (q : Loc), RET #q;
      match st.becomeLeader (uint.nat i) with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
