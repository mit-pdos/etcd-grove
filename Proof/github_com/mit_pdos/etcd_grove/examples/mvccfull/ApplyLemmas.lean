/-
mvccfull's `runner.apply`: lemmas of the operations that change nothing in the model (a commit, a
read, the leases' check) and of the member's record after an operation. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.StepModel

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- **An operation that makes no revision, compacts nothing and grants or revokes no lease leaves
the model as it was.** -/
theorem runM_succ_same (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o)
    (hk : o.kind = kCommit ∨ o.kind = kRead ∨ o.kind = kLeases ∨ (o.kind = kTxn ∧ o.write = false)) :
    runM ks ops (n + 1) = runM ks ops n := by
  rw [runM_succ ks ops n o ho]
  have hkp : o.kind ≠ kPut := by rcases hk with h | h | h | ⟨h, -⟩ <;> rw [h] <;> decide
  have hkd : o.kind ≠ kDelete := by rcases hk with h | h | h | ⟨h, -⟩ <;> rw [h] <;> decide
  have hkg : o.kind ≠ kGrant := by rcases hk with h | h | h | ⟨h, -⟩ <;> rw [h] <;> decide
  have hkr : o.kind ≠ kRevoke := by rcases hk with h | h | h | ⟨h, -⟩ <;> rw [h] <;> decide
  have hkc : o.kind ≠ kCompact := by rcases hk with h | h | h | ⟨h, -⟩ <;> rw [h] <;> decide
  have hP : (opPend ks (runM ks ops n) o).chs = [] := by
    unfold opPend
    simp only [hkp, hkd, hkr, ↓reduceIte]
    by_cases ht : o.kind = kTxn
    · have hw : o.write = false := by
        rcases hk with h | h | h | ⟨-, h⟩
        · rw [h] at ht; exact absurd ht (by decide)
        · rw [h] at ht; exact absurd ht (by decide)
        · rw [h] at ht; exact absurd ht (by decide)
        · exact h
      simp only [ht, hw, ↓reduceIte, Bool.false_eq_true]
    · simp only [ht, ↓reduceIte]
  unfold opStep
  simp only [hkg, hkr, hkc, false_and, decide_false, Bool.false_eq_true, ↓reduceIte]
  unfold histAfter
  simp only [hP, ↓reduceIte]

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The member after an operation that changes nothing in the model**: its record with one more
operation applied. -/
theorem memCore_succ_same (ks : List GoString) (γh : HistNames) (ops : List OpM) (i : Nat)
    (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat)
    (h : runM ks ops (v.ops + 1) = runM ks ops v.ops) (hl : v.ops + 1 ≤ ops.length) :
    memCore (GF := GF) ks γh ops i mp m f v qw nw k ⊢
      memCore ks γh ops i mp m f { v with ops := v.ops + 1 } qw nw k := by
  unfold memCore σOf revAfter cmpAfter leasesAfter grantedAfter histAt
  simp only [h]
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, %H11, H12⟩
  iframe
  ipureintro; exact hl

/-- The leader's history part after an operation that changes nothing in the model. -/
theorem leadPost_same (γh : HistNames) (ks : List GoString) (ops : List OpM) (n : Nat) (lead : Bool)
    (h : runM ks ops (n + 1) = runM ks ops n) :
    leadPre (GF := GF) γh ks ops n lead ⊢ leadPost γh ks ops n lead := by
  unfold leadPre leadPost histAt compsAt
  cases lead
  · simp only [Bool.false_eq_true, ↓reduceIte]; iintro -; itrivial
  · simp only [↓reduceIte, h]; iintro H; iexact H

/-- **The history's lower bound at the member's count**, from either history part. -/
theorem leadPre_lb (γh : HistNames) (ks : List GoString) (ops : List OpM) (n : Nat) (lead : Bool) :
    leadPre (GF := GF) γh ks ops n lead ⊢
      leadPre γh ks ops n lead ∗ monoListLbOwn γh.l (histAt ks ops n) := by
  unfold leadPre
  cases lead
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro #H
    isplitl; · iexact H
    iapply monoListLbOwn_le _ (runM_hs_prefix ks ops n (n + 1) (Nat.le_succ n))
    iexact H
  · simp only [↓reduceIte]
    iintro H
    iapply histW_lb
    iexact H

end lemmas

end mvccfull
end EtcdGrove
end Perennial
