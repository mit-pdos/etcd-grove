/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.HandleAppendEntriesRequest(i, j, m)`: the action `HandleAppendEntriesRequest(i, j, m)`, snapshots aside.
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

/-- `s.HandleAppendEntriesRequest(i, j, m)`, of a server `i` of the state whose bags the Go's `Bag`
handles (`Bag.Ok`), the request not a snapshot, its `prevLogIndex` in `[0, 2^62 - 1)` and the logs far
from overflow (`AcceptAppendEntriesRequest`'s premises): `handleAppendEntriesRequest i j m`'s
successors (it never fails off snapshots), new read-only states, in order. -/
abbrev State.HandleAppendEntriesRequest.spec : Prop :=
  ∀ (p : Loc) (st : State) (i j : w64) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ msgRO q m ∗
      ⌜uint.nat i ∈ st.server ∧ st.pendingMessages.Ok ∧ st.messages.Ok ∧ m.subtype ≠ "snapshot" ∧
        0 ≤ m.prevLogIndex ∧ m.prevLogIndex + 1 < 2 ^ 62 ∧
        (st.s (uint.nat i)).log.length < 2 ^ 62 ∧ m.entries.length < 2 ^ 62⌝ }}
    (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"HandleAppendEntriesRequest")) (Val #i)) (Val #j)) (Val #q))
  {{ (out : GoSlice), RET #out;
      match st.handleAppendEntriesRequest (uint.nat i) (uint.nat j) m with
      | .ok sts => ∃ qs : List Loc, out ↦* qs ∗ ownSliceCap Loc out (DFrac.own 1) ∗
          [∗list] r;s ∈ qs;sts, stateRO r s
      | .error _ => False }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
