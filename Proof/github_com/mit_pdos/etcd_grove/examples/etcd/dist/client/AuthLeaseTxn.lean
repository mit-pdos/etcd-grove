/-
**u's leased transaction at the cluster view** (F7 stage S5, `notes/etcd-dist-f7.md`, "Handoff S5-4"): the
shape facts `Txn_CommitOn_dist`'s widened write arm asks of `Txn().Then(OpPut(k, "v", WithLease(L)))`
(writing, fits a gRPC message, leased: `txnPlainL`, no zero range end), and `OpPut(k, "v", WithLease(L))`'s
transaction operation. Ports of authlease `run.lean`'s `leaseTxn_ok`/`txnOpOf_leasePut` (a proof module) into a
defs module, without the single-process contract's `kvShapeAll`/`txnNestOk`, which the dist contract does not
ask. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseRefusals
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open client go_etcd_io.etcd.server.v3.etcdserver etcd_authlease

section pure
variable [GooseExts]

/-- **u's leased transaction's shape** (`Txn_CommitOn_dist`'s write arm and size premise):
`Txn().Then(OpPut(k, "v", WithLease(L)))` writes, fits a gRPC message, is leased (`txnPlainL`), and has no
zero range end. -/
theorem leaseTxnD_ok (k : GoString) (L : w64) (hkl : k.length ≤ 2 ^ 20) :
    txn.txnReadonly (txnWireOf (leaseTxn k L)) = false ∧ txnSizeOk (txnWireOf (leaseTxn k L)) ∧
    txnPlainL (txnWireOf (leaseTxn k L)) ∧ txnNoZeroEnd (txnWireOf (leaseTxn k L)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [leaseTxn, txnWireOf, opWire, txn.txnReadonly, txn.opIsGet]
  · refine txnSizeOk_of_bounds (N := 2 ^ 20) (M := 3) ⟨?_, ?_, ?_⟩ ?_ (by decide)
    · intro c hc; simp [leaseTxn, txnWireOf] at hc
    · intro o ho
      simp [leaseTxn, txnWireOf, opWire] at ho
      subst ho
      simp only [TxnOp.bytesLe]; exact ⟨hkl, by decide⟩
    · intro o ho; simp [leaseTxn, txnWireOf] at ho
    · simp [TxnModel.nodes, leaseTxn, txnWireOf, opWire, TxnOp.nodes]
  · simp [txnPlainL, txn.txnLeased, leaseTxn, txnWireOf, opWire, txn.opsLeased, txn.opLeased]
  · refine ⟨by simp [leaseTxn, txnWireOf], ?_, by simp [leaseTxn, txnWireOf, txnOpsNoZeroEnd]⟩
    simp [leaseTxn, txnWireOf, opWire, txnOpsNoZeroEnd, txnOpNoZeroEnd]

/-- `OpPut(k, "v", WithLease(L))`'s transaction operation. -/
theorem txnOpOf_leasePutD (k : GoString) (L : w64) :
    txnOpOf (opPutModel k go!"v" [withLeaseM L]) = some (.put k go!"v" L) := by
  simp [txnOpOf, opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]

end pure

end etcd_dist_client
end EtcdGrove
end Perennial
