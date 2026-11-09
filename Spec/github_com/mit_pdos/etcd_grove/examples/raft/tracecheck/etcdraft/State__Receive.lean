/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.Receive(m)`: `Receive(m) == ReceiveDirect(m)`, every successor (pre-vote and snapshots aside).
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

/-- `s.Receive(m)`, of a state whose bags the Go's `Bag` handles (`Bag.Ok`), the message not a
pre-vote one (`HandlePreVoteRequest`/`HandlePreVoteResponse` are not specified) nor a snapshot, its
`prevLogIndex` in `[0, 2^62 - 1)` and its entries and its destination's log (when a server) far from
overflow: `receive m`'s successors (it never fails off snapshots), new read-only states, in order. -/
abbrev State.Receive.spec : Prop :=
  ∀ (p : Loc) (st : State) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ msgRO q m ∗
      ⌜st.pendingMessages.Ok ∧ st.messages.Ok ∧ m.type ≠ .preVoteRequest ∧ m.type ≠ .preVoteResponse ∧
        m.subtype ≠ "snapshot" ∧ 0 ≤ m.prevLogIndex ∧ m.prevLogIndex + 1 < 2 ^ 62 ∧
        m.entries.length < 2 ^ 62 ∧ (m.dest ∈ st.server → (st.s m.dest).log.length < 2 ^ 62)⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"Receive")) (Val #q))
  {{ (out : GoSlice), RET #out;
      match st.receive m with
      | .ok sts => ∃ qs : List Loc, out ↦* qs ∗ ownSliceCap Loc out (DFrac.own 1) ∗
          [∗list] r;s ∈ qs;sts, stateRO r s
      | .error _ => False }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
