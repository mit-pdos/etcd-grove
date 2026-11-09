/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.AdvanceCommitIndex(i)`: the action `AdvanceCommitIndex(i)`.
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

/-- `s.AdvanceCommitIndex(i)`, of a server `i` of the state whose configuration and log are far from
overflow (fewer than `2^62` members, `IsQuorum`'s premise; fewer than `2^62` entries):
`advanceCommitIndex i`'s successor, a new read-only state, or `nil` where it is not enabled. -/
abbrev State.AdvanceCommitIndex.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗
      ⌜uint.nat i ∈ st.server ∧ (st.getConfig (uint.nat i)).length < 2 ^ 62 ∧
        (st.s (uint.nat i)).log.length < 2 ^ 62⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"AdvanceCommitIndex")) (Val #i))
  {{ (q : Loc), RET #q;
      match st.advanceCommitIndex (uint.nat i) with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
