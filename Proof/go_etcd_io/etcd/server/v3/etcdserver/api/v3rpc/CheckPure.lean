/-
The request checks' pure consequences (unit 1 of the request path): what passing
`checkTxnRequest`/`checkRequestOp` says of a transaction, purely. Lean-first (no Rocq
counterpart).

* `opCheck_toTxnOp`/`opsCheck_toTxnOps`: an operation (a list of operations) that passes has a
  transaction model (`ReqOp.toTxnOp`): no empty `RequestOp` at any depth. This is the txn
  package's `etcd-txn-empty-requestop` precondition (`txn.requestOpIs` has no empty oneof:
  `executeTxn` dereferences the `nil` response `newTxnResp` leaves for one), discharged at the
  API: `checkRequestOp` rejects an empty one with `ErrGRPCKeyNotFound`.
* `txnCheck_ok_iff`: `checkTxnRequest(r, n)` passes iff the widest of the comparisons and the
  branches is at most `n`, every comparison has a key, and every operation of both branches
  passes `checkRequestOp` at `n` less that width (the budget per level:
  `issues/etcd-max-txn-ops-nested.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

theorem opsCheck_none_iff (n : Int) (us : List ReqOp) :
    opsCheck n us = none ↔ ∀ u ∈ us, opCheck n u = none := by
  induction us with
  | nil => simp [opsCheck]
  | cons u us ih =>
    simp only [opsCheck, List.mem_cons, forall_eq_or_imp]
    cases h : opCheck n u with
    | some e => simp
    | none => simp [ih]

mutual
/-- **A checked operation is not empty**, at any depth: it has a transaction model. -/
theorem opCheck_toTxnOp : ∀ (n : Int) (u : ReqOp), opCheck n u = none →
    (ReqOp.toTxnOp u).isSome = true
  | _, .range _, _ => by simp [ReqOp.toTxnOp]
  | _, .put _, _ => by simp [ReqOp.toTxnOp]
  | _, .delete _, _ => by simp [ReqOp.toTxnOp]
  | n, .txn cs ts es, h => by
    simp only [opCheck] at h
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i hts
    have h1 := opsCheck_toTxnOps _ ts hts
    have h2 := opsCheck_toTxnOps _ es h
    simp only [ReqOp.toTxnOp]
    obtain ⟨ts', hts'⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨es', hes'⟩ := Option.isSome_iff_exists.1 h2
    rw [hts', hes']
    rfl
  | _, .empty, h => by simp [opCheck] at h

/-- **Checked operations are not empty**, at any depth: they have a transaction model. -/
theorem opsCheck_toTxnOps : ∀ (n : Int) (us : List ReqOp), opsCheck n us = none →
    (ReqOp.toTxnOps us).isSome = true
  | _, [], _ => by simp [ReqOp.toTxnOps]
  | n, u :: us, h => by
    simp only [opsCheck] at h
    split at h
    · simp at h
    rename_i hu
    have h1 := opCheck_toTxnOp n u hu
    have h2 := opsCheck_toTxnOps n us h
    simp only [ReqOp.toTxnOps]
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.1 h2
    rw [ht, hts]
    rfl
end

/-- **An empty operation is rejected** (`ErrGRPCKeyNotFound`). -/
theorem opCheck_empty (n : Int) : opCheck n .empty = some .keyNotFound := rfl

/-- **`checkTxnRequest`, purely** (see the file header). -/
theorem txnCheck_ok_iff (n : Int) (cs : List CmpModel) (ts es : List ReqOp) :
    txnReqOk n cs ts es ↔
      (txnWidth cs ts es : Int) ≤ n ∧ (∀ c ∈ cs, c.key ≠ []) ∧
        (∀ u ∈ ts, requestOpOk (n - txnWidth cs ts es) u) ∧
        (∀ u ∈ es, requestOpOk (n - txnWidth cs ts es) u) := by
  unfold txnReqOk txnCheck requestOpOk
  simp only [opCheck]
  by_cases hw : n < txnWidth cs ts es
  · simp only [hw, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    intro h; omega
  · simp only [hw, ↓reduceIte]
    by_cases hc : cs.any (fun c => decide (c.key = [])) = true
    · simp only [hc, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro _ hk
      obtain ⟨c, hc1, hc2⟩ := List.any_eq_true.1 hc
      exact absurd (of_decide_eq_true hc2) (hk c hc1)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hk : ∀ c ∈ cs, c.key ≠ [] := by
        intro c h1 h2
        exact hc (List.any_eq_true.2 ⟨c, h1, by simp [h2]⟩)
      cases h1 : opsCheck (n - ↑(txnWidth cs ts es)) ts with
      | some e =>
        simp only [reduceCtorEq, false_iff, not_and]
        intro _ _ hts
        have := (opsCheck_none_iff _ ts).2 hts
        rw [this] at h1; cases h1
      | none =>
        simp only [(opsCheck_none_iff _ ts).1 h1, opsCheck_none_iff]
        constructor
        · intro h; exact ⟨by omega, hk, fun u hu => (opsCheck_none_iff _ ts).1 h1 u hu, h⟩
        · intro h; exact h.2.2.2

/-- **A transaction that passes `checkTxnRequest` has a transaction model** (no empty
operation at any depth): the txn package's `TxnModel` of its comparisons and branches. -/
theorem txnCheck_toTxnOps {n : Int} {cs : List CmpModel} {ts es : List ReqOp}
    (h : txnReqOk n cs ts es) :
    ∃ ts' es', ReqOp.toTxnOps ts = some ts' ∧ ReqOp.toTxnOps es = some es' := by
  have h' := opCheck_toTxnOp n (.txn cs ts es) h
  simp only [ReqOp.toTxnOp] at h'
  split at h'
  · rename_i ts' es' h1 h2; exact ⟨ts', es', h1, h2⟩
  · simp at h'

end v3rpc
end EtcdGrove
end Perennial
