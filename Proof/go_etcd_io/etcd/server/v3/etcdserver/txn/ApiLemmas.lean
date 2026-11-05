/-
The txn proofs' lemmas over mvcc's API (strict M1, 2026-11-05): a transaction's and a store
handle's dynamic type meets its interface's contracts (from `shapes.law`), keeping the resource.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiVocab

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

/-- A reachable state's log has `NewStore`'s two revisions. -/
theorem txn.reach_len (σ : MvccState) (h : mvcc.api.MvccReachable σ) : 2 ≤ σ.log.length := by
  induction h with
  | start => decide
  | notify σ pend _ _ _ ih => exact ih
  | commit σ _ ih =>
    unfold mvcc.api.MvccState.commitPending mvcc.commitLog
    split
    · exact ih
    · simp only [List.length_append, List.length_singleton]; omega
  | compact σ r _ _ _ _ _ ih => exact ih

/-- A transaction's begin state after changes. -/
theorem txn.MTxn.append_state (k : MTxn) (chs : List mvcc.Change) :
    (txn.MTxn.append k chs).state = k.state := by cases k <;> rfl

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **A transaction is an interface value whose type meets `TxnWrite`'s contracts**
(`shapes.law`), the transaction kept. -/
theorem txn.mvccTxn_shape (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) :
    mvcc.api.mvccTxn (GF := GF) t γ trace k ⊢
      ⌜∃ ty v, t = interface.mkOk ty v ∧ mvcc.api.isTxn (GF := GF) ty v⌝ ∗
        mvcc.api.mvccTxn t γ trace k :=
  persistent_entails_right (hsh.2.2.1 t γ trace k)

/-- **A store handle is an interface value whose type meets `KV`'s contracts** (`shapes.law`),
the handle kept. -/
theorem txn.isMvcc_shape (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (kv : GoInterface) (γ : MvccName) :
    mvcc.api.isMvcc (GF := GF) kv γ ⊢
      ⌜∃ ty v, kv = interface.mkOk ty v ∧ mvcc.api.isKV (GF := GF) ty v⌝ ∗ mvcc.api.isMvcc kv γ :=
  persistent_entails_right (hsh.1 kv γ)

end lemmas

end EtcdGrove
end Perennial
