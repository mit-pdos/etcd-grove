/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.RequestVote(i, j)`: the action `RequestVote(i, j)`.
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

/-- `s.RequestVote(i, j)`, of a server `i` of the state whose pending bag the Go's `Bag` handles
(`Bag.Ok`): `requestVote i j`'s successor, a new read-only state, or `nil` where it is not enabled. -/
abbrev State.RequestVote.spec : Prop :=
  ∀ (p : Loc) (st : State) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ ⌜uint.nat i ∈ st.server ∧ st.pendingMessages.Ok⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"RequestVote")) (Val #i)) (Val #j))
  {{ (q : Loc), RET #q;
      match st.requestVote (uint.nat i) (uint.nat j) with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
