/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.ReturnToFollowerState(i, m)`: the action `ReturnToFollowerState(i, m)`.
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

/-- `s.ReturnToFollowerState(i, m)`, of a server `i` of the state: `returnToFollowerState i m`'s
successor, a new state (a clone the caller owns, `HandleAppendEntriesRequest` writes it), or `nil`
where it is not enabled. -/
abbrev State.ReturnToFollowerState.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ msgRO q m ∗ ⌜uint.nat i ∈ st.server⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"ReturnToFollowerState")) (Val #i)) (Val #q))
  {{ (r : Loc), RET #r;
      match st.returnToFollowerState (uint.nat i) m with
      | none => ⌜r = null⌝
      | some st' => ∃ M, stateOwn r st' M }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
