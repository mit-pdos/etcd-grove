/-
**The protobuf depth of an `InternalRaftRequest`** (2026-10-31, `notes/irr-depth.md`;
`issues/etcd-txn-nested-depth-apply-panic.md`): the vocabulary of `proto.MarshalIRR.spec`'s
premise. protobuf-go's `proto.Unmarshal` (v1.36.12) refuses a message nested more than
`protowire.DefaultRecursionLimit` (10000) levels deep, the top one counted; `pbutil.
MustUnmarshalMessage` panics on it at apply. The only recursion of `raft_internal.proto`'s request
is its transaction (`TxnRequest`/`RequestOp`), so the request's depth is its transaction's plus
one; every other field is at most two levels below the request. Lean-first (no Rocq counterpart).

Kept out of `cache/v3/InvEtcdTxn.lean` (beside `TxnModel`), which the whole cache and client
import, so that the vocabulary does not rebuild them.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **protobuf-go's default recursion limit** (`protowire.DefaultRecursionLimit`, v1.36.12
`encoding/protowire/wire.go:28`): `proto.Unmarshal` decodes a message whose every message is at
most this many levels deep, the top one counted (`internal/impl/decode.go:105`). -/
def apply.protoRecursionLimit : Nat := 10000

/-- The deepest of a list of depths (`0` for none). -/
def apply.depthMax (l : List Nat) : Nat := l.foldr max 0

/-- **An operation's protobuf depth**: the levels of its `RequestOp` message and below. A get, a
put, a delete: the `RequestOp` and its `RangeRequest`/`PutRequest`/`DeleteRangeRequest` (2). A
nested transaction: the `RequestOp`, its `TxnRequest`, and the deepest of its comparisons (a
`Compare`, 1) and operations. (The oneof wrapper `RequestOp_RequestTxn` is no message.) -/
def TxnOp.msgDepth : TxnOp → Nat
  | .txn cs ts es => 2 + max (if cs = [] then 0 else 1)
      (max (apply.depthMax (ts.map TxnOp.msgDepth)) (apply.depthMax (es.map TxnOp.msgDepth)))
  | _ => 2

/-- **A transaction's protobuf depth**: its `TxnRequest` and below. -/
def TxnModel.msgDepth (t : TxnModel) : Nat :=
  1 + max (if t.cmps = [] then 0 else 1)
    (max (apply.depthMax (t.thenOps.map TxnOp.msgDepth))
      (apply.depthMax (t.elseOps.map TxnOp.msgDepth)))

/-- **A transaction whose `InternalRaftRequest` decodes**: one level for the request around it,
within the limit. -/
def apply.txnDepthOk (t : TxnModel) : Prop := t.msgDepth + 1 ≤ apply.protoRecursionLimit

/-- **A request within protobuf-go's recursion limit** (`proto.MarshalIRR.spec`'s premise): its
transaction, if any (`IRRModel.txn`, the wire transaction's model: `toModel` keeps the tree). The
other fields are at most two levels below the request (see the MarshalIRR header). -/
def apply.irrDepthOk (rq : apply.IRRModel) : Prop :=
  ∀ t, rq.txn = some t → apply.txnDepthOk t

/-! ## Laws -/

theorem apply.depthMax_le {l : List Nat} {n : Nat} (h : ∀ d ∈ l, d ≤ n) :
    apply.depthMax l ≤ n := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons d l ih =>
    simp only [apply.depthMax, List.foldr_cons] at ih ⊢
    exact Nat.max_le.2 ⟨h d (List.mem_cons_self ..), ih (fun d' hd => h d' (List.mem_cons_of_mem _ hd))⟩

theorem apply.irrDepthOk_of_txn_none {rq : apply.IRRModel} (h : rq.txn = none) :
    apply.irrDepthOk rq := by
  intro t ht; rw [h] at ht; cases ht

theorem apply.irrDepthOk_of_txnW_none {rq : apply.IRRModel} (h : rq.txnW = none) :
    apply.irrDepthOk rq :=
  apply.irrDepthOk_of_txn_none (by simp [apply.IRRModel.txn, h])

theorem apply.txnDepthOk_mono {t : TxnModel} {n : Nat} (h : t.msgDepth ≤ n)
    (hn : n + 1 ≤ apply.protoRecursionLimit) : apply.txnDepthOk t := by
  unfold apply.txnDepthOk; omega

/-- A request of a kind `dispatch` tests after `.txn` has no transaction. -/
theorem apply.txn_none_of_dispatchKind {rq : apply.IRRModel}
    (h : apply.dispatchKind rq ≠ .clusterVersionSet ∧ apply.dispatchKind rq ≠ .clusterMemberAttrSet ∧
      apply.dispatchKind rq ≠ .downgradeInfoSet ∧ apply.dispatchKind rq ≠ .downgradeVersionTest ∧
      apply.dispatchKind rq ≠ .range ∧ apply.dispatchKind rq ≠ .put ∧
      apply.dispatchKind rq ≠ .deleteRange ∧ apply.dispatchKind rq ≠ .txn) :
    rq.txn = none := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  cases ht : rq.txn with
  | none => rfl
  | some t =>
    exfalso
    by_cases c1 : rq.clusterVersionSet.isSome = true
    · exact h1 (by simp [apply.dispatchKind, c1])
    by_cases c2 : rq.clusterMemberAttrSet.isSome = true
    · exact h2 (by simp [apply.dispatchKind, c1, c2])
    by_cases c3 : rq.downgradeInfoSet.isSome = true
    · exact h3 (by simp [apply.dispatchKind, c1, c2, c3])
    by_cases c4 : rq.downgradeVersionTest = true
    · exact h4 (by simp [apply.dispatchKind, c1, c2, c3, c4])
    by_cases c5 : rq.range.isSome = true
    · exact h5 (by simp [apply.dispatchKind, c1, c2, c3, c4, c5])
    by_cases c6 : rq.put.isSome = true
    · exact h6 (by simp [apply.dispatchKind, c1, c2, c3, c4, c5, c6])
    by_cases c7 : rq.deleteRange.isSome = true
    · exact h7 (by simp [apply.dispatchKind, c1, c2, c3, c4, c5, c6, c7])
    exact h8 (by simp [apply.dispatchKind, c1, c2, c3, c4, c5, c6, c7, ht])

end EtcdGrove
end Perennial
