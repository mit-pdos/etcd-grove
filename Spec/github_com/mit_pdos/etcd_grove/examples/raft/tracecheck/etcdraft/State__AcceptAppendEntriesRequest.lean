/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.AcceptAppendEntriesRequest(i, j, logOk, m)`: the action `AcceptAppendEntriesRequest(i, j, logOk, m)`, snapshots aside.
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

/-- `s.AcceptAppendEntriesRequest(i, j, logOk, m)`, of a server `i` of the state whose bags the Go's
`Bag` handles (`Bag.Ok`), the request not a snapshot (`HandleSnapshotRequest` is not specified), its
`prevLogIndex` in `[0, 2^62 - 1)` and the logs far from overflow: `acceptAppendEntriesRequest i j logOk
m`'s successors (it never fails off snapshots), new states the caller owns, in order. -/
abbrev State.AcceptAppendEntriesRequest.spec : Prop :=
  ∀ (p : Loc) (st : State) (i j : w64) (logOk : Bool) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ msgRO q m ∗
      ⌜uint.nat i ∈ st.server ∧ st.pendingMessages.Ok ∧ st.messages.Ok ∧ m.subtype ≠ "snapshot" ∧
        0 ≤ m.prevLogIndex ∧ m.prevLogIndex + 1 < 2 ^ 62 ∧
        (st.s (uint.nat i)).log.length < 2 ^ 62 ∧ m.entries.length < 2 ^ 62⌝ }}
    (App (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"AcceptAppendEntriesRequest")) (Val #i)) (Val #j)) (Val #logOk)) (Val #q))
  {{ (out : GoSlice), RET #out;
      match st.acceptAppendEntriesRequest (uint.nat i) (uint.nat j) logOk m with
      | .ok sts => ∃ qs : List Loc, out ↦* qs ∗ ownSliceCap Loc out (DFrac.own 1) ∗
          [∗list] r;s ∈ qs;sts, ∃ M, stateOwn r s M
      | .error _ => False }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
