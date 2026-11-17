/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.ConflictAppendEntriesRequest(i, index, m)`: the action `ConflictAppendEntriesRequest(i, index, m)`.
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

/-- `s.ConflictAppendEntriesRequest(i, index, m)`, of a server `i` of the state, an index at least 1
and the logs far from overflow (`HasNoConflict`'s premises): `conflictAppendEntriesRequest i index
m`'s successor (it never fails: `SubSeq(log, 1, Len(log) - 1)` is defined), a new state (a clone the
caller owns, `HandleAppendEntriesRequest` writes it), or `nil` where it is not enabled. -/
abbrev State.ConflictAppendEntriesRequest.spec : Prop :=
  ∀ (p : Loc) (st : State) (i index : w64) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ msgRO q m ∗
      ⌜uint.nat i ∈ st.server ∧ 1 ≤ sint.Z index ∧ sint.Z index < 2 ^ 62 ∧
        (st.s (uint.nat i)).log.length < 2 ^ 62 ∧ m.entries.length < 2 ^ 62⌝ }}
    (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"ConflictAppendEntriesRequest")) (Val #i)) (Val #index)) (Val #q))
  {{ (r : Loc), RET #r;
      match st.conflictAppendEntriesRequest (uint.nat i) (sint.Z index) m with
      | .ok none => ⌜r = null⌝
      | .ok (some st') => ∃ M, stateOwn r st' M
      | .error _ => False }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
