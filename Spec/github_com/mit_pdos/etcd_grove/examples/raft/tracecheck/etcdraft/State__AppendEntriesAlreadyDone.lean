/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.AppendEntriesAlreadyDone(i, j, index, m)`: the action `AppendEntriesAlreadyDone(i, j, index, m)`.
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

/-- `s.AppendEntriesAlreadyDone(i, j, index, m)`, of a server `i` of the state whose bags the Go's
`Bag` handles (`Bag.Ok`), an index at least 1 and the message's numbers and the logs far from
overflow (`HasNoConflict`'s premises): `appendEntriesAlreadyDone i j index m`'s successor, a new
state (a clone the caller owns, `HandleAppendEntriesRequest` writes it), or `nil` where it is not
enabled. -/
abbrev State.AppendEntriesAlreadyDone.spec : Prop :=
  ∀ (p : Loc) (st : State) (i j index : w64) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ msgRO q m ∗
      ⌜uint.nat i ∈ st.server ∧ st.pendingMessages.Ok ∧ st.messages.Ok ∧
        1 ≤ sint.Z index ∧ sint.Z index < 2 ^ 62 ∧ 0 ≤ m.prevLogIndex ∧ m.prevLogIndex < 2 ^ 62 ∧
        (st.s (uint.nat i)).log.length < 2 ^ 62 ∧ m.entries.length < 2 ^ 62⌝ }}
    (App (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"AppendEntriesAlreadyDone")) (Val #i)) (Val #j)) (Val #index)) (Val #q))
  {{ (r : Loc), RET #r;
      match st.appendEntriesAlreadyDone (uint.nat i) (uint.nat j) (sint.Z index) m with
      | none => ⌜r = null⌝
      | some st' => ∃ M, stateOwn r st' M }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
