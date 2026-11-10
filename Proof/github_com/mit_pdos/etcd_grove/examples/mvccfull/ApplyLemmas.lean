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

/-- **A grant's model step**: the history and the compaction revision unchanged, the id appended
to the live and the granted leases. -/
theorem runM_succ_grant (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o) (hk : o.kind = kGrant) :
    histAt ks ops (n + 1) = histAt ks ops n ∧ cmpAfter ks ops (n + 1) = cmpAfter ks ops n ∧
      leasesAfter ks ops (n + 1) = leasesAfter ks ops n ++ [o.id] ∧
      grantedAfter ks ops (n + 1) = grantedAfter ks ops n ++ [o.id] := by
  unfold histAt cmpAfter leasesAfter grantedAfter
  rw [runM_succ ks ops n o ho]
  have hP : (opPend ks (runM ks ops n) o).chs = [] := by
    unfold opPend; rw [hk]; simp
  unfold opStep
  rw [hk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show histAfter _ _ = _; unfold histAfter; simp only [hP, ↓reduceIte]
  · simp
  · simp
  · simp

/-- **A put's or a delete's model step** leaves the compaction revision, the leases and the
compactions. -/
theorem runM_succ_pd (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o) (hk : o.kind = kPut ∨ o.kind = kDelete) :
    cmpAfter ks ops (n + 1) = cmpAfter ks ops n ∧ leasesAfter ks ops (n + 1) = leasesAfter ks ops n ∧
      grantedAfter ks ops (n + 1) = grantedAfter ks ops n ∧ compsAt ks ops (n + 1) = compsAt ks ops n := by
  unfold cmpAfter leasesAfter grantedAfter compsAt
  rw [runM_succ ks ops n o ho]
  unfold opStep
  rcases hk with hk | hk <;> rw [hk] <;> simp

theorem σOf_succ_grant (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o) (hk : o.kind = kGrant) : σOf ks ops (n + 1) = σOf ks ops n := by
  obtain ⟨h1, h2, -, -⟩ := runM_succ_grant ks ops n o ho hk
  unfold σOf; rw [h1, h2]

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Each revision of a member's log has fewer than `2 ^ 63` changes**: its changes' keys are
distinct (`logOk_once`) and among the keys `ks` (a put's key is one, a delete's a present key),
fewer than `2 ^ 63` (a slice's). (To prove: an induction over `runM` that every change's key is in
`ks`, from `opValid`/`subsOk` and `stMatch`; `sorry` for now.) -/
theorem log_cs_lt (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (h : logOk ks ops) (hksl : ks.length < 2 ^ 63) (n : Nat) :
    ∀ cs ∈ (σOf ks ops n).log, cs.length < 2 ^ 63 := by
  sorry

/-- **What a write transaction at a member's state needs of the model** (`begin`'s, `writeRange`'s,
`writeSub`'s premises). -/
theorem member_facts (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (h : logOk ks ops) (hksl : ks.length < 2 ^ 63) (n : Nat) (hn : n ≤ ops.length)
    (h38 : ops.length < 2 ^ 38) :
    (histAt ks ops n).length = (σOf ks ops n).log.length ∧
      HistRevs ks (σOf ks ops n).log (histAt ks ops n) ∧ MvccReachable (σOf ks ops n) ∧
      txn.LogOk ((σOf ks ops n).log ++ [[]]) ∧ (σOf ks ops n).log.length + 3 ≤ 2 ^ 63 ∧
      stMatch ks (lastSt (histAt ks ops n)) (stateAfter (σOf ks ops n).log) ∧
      (σOf ks ops n).pending = none ∧ (σOf ks ops n).rev + 2 < 2 ^ 40 ∧
      onceUpToAll (σOf ks ops n).log := by
  have hlen : (histAt ks ops n).length = (σOf ks ops n).log.length := by
    simp [σOf, logOfHist_length]
  have hl := runM_hs_len ks ops n
  have hlh : (histAt ks ops n).length = (runM ks ops n).hs.length := rfl
  obtain ⟨-, hh, hreach⟩ := logOk_hist ks hks ops h n n (Nat.le_refl _) hn
  have hinv := runM_inv ks ops h n
  obtain ⟨-, -, hst, -, hnd⟩ := hinv
  obtain ⟨-, hwf, -⟩ := hnd (nodup_of_sorted hks)
  have hlog : (σOf ks ops n).log = logOfHist (runM ks ops n).hs := rfl
  have hne : (σOf ks ops n).log ≠ [] := by
    intro h0; have := congrArg List.length h0; simp only [List.length_nil] at this; omega
  refine ⟨hlen, ?_, hreach, ?_, ?_, ?_, rfl, ?_, logOk_once ks hks ops h n⟩
  · intro r hr
    have := hh.2 r (by rw [σOf_notified]; exact hr)
    rwa [σOf_notified] at this
  · refine txn.LogOk.of_cert ⟨LogWf'.append_nil (LogWf'.of_wf (by rw [hlog]; exact hwf)) hne,
      by simp; omega, ?_⟩ (by simp)
    intro cs hcs
    simp only [List.mem_append, List.mem_singleton] at hcs
    rcases hcs with hc | hc
    · exact log_cs_lt ks hks ops h hksl n cs hc
    · subst hc; simp
  · omega
  · obtain ⟨e, he⟩ : ∃ e, (runM ks ops n).hs[(runM ks ops n).hs.length - 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have := hst _ e he
    have hl1 : lastSt (histAt ks ops n) = e.1 := lastSt_of he
    rw [hl1, ← hlog] at *
    rw [← stateAt_last (σOf ks ops n).log (by rw [← hlen]; omega)]
    rw [← hlen]; exact this
  · unfold MvccState.rev; omega


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

/-- **`apply`'s close for an operation that changes nothing in the model**: the member with one
more operation applied, the hook's counters at the operation's index. -/
theorem apply_close_same (ks : List GoString) (γh : HistNames) (ops : List OpM) (i : Nat)
    (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat) (lead : Bool)
    (s0 : w64) (h : runM ks ops (v.ops + 1) = runM ks ops v.ops) (hl : v.ops + 1 ≤ ops.length)
    (h38 : v.ops < 2 ^ 38) (hs : sint.Z s0 ≤ sint.Z (W64 ((v.ops + 1 : Nat) : Int))) :
    memCore (GF := GF) ks γh ops i mp m f v qw nw k ∗ leadPre γh ks ops v.ops lead ∗
        sync.atomic.ownInt64 (mF go!"applying" mp) (DFrac.own 1) (W64 ((v.ops + 1 : Nat) : Int)) ∗
        sync.atomic.ownInt64 (mF go!"saved" mp) (DFrac.own 1) s0 ∗
        mF go!"ops" mp ↦ (W64 ((v.ops + 1 : Nat) : Int)) ⊢
      leadPost γh ks ops v.ops lead ∗
        ∃ (v' : MemS) (k' : Nat), ⌜MemS.sameInc v v' ∧ v'.ops = v.ops + 1 ∧ k ≤ k' + 1⌝ ∗
          memW ks γh ops i mp m f v' qw nw k' := by
  iintro ⟨Hmc, Hlead, Happ, Hsav, Hops⟩
  isplitl [Hlead]
  · iapply leadPost_same γh ks ops v.ops lead h; iexact Hlead
  iexists { v with ops := v.ops + 1 }, k
  isplitr
  · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, by omega⟩
  iunfold memW
  isplitl [Hops]
  · iexact Hops
  isplitl [Happ Hsav]
  · iexists _, _; iunfold hookPre; iframe; ipureintro
    have : sint.Z (W64 ((v.ops + 1 : Nat) : Int)) = v.ops + 1 := by word
    refine ⟨hs, by omega, by simp only; omega⟩
  iapply memCore_succ_same ks γh ops i mp m f v qw nw k h hl
  iexact Hmc

/-- **`apply`'s close after an operation's own function** (`txn`, `compact`): the member's record
with the hook's counters at the operation's index (run or not). -/
theorem memW_of_core (ks : List GoString) (γh : HistNames) (ops : List OpM) (i : Nat)
    (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat) (n : Nat) (s0 : w64)
    (hv : v.ops = n + 1) (h38 : n < 2 ^ 38) (_hs : sint.Z s0 < sint.Z (W64 ((n + 1 : Nat) : Int))) :
    memCore (GF := GF) ks γh ops i mp m f v qw nw k ∗
        (hookPost mp (W64 ((n + 1 : Nat) : Int)) ∨ hookPre mp (W64 ((n + 1 : Nat) : Int)) s0) ∗
        mF go!"ops" mp ↦ (W64 ((n + 1 : Nat) : Int)) ⊢
      memW ks γh ops i mp m f v qw nw k := by
  have hz : sint.Z (W64 ((n + 1 : Nat) : Int)) = n + 1 := by word
  iintro ⟨Hmc, Hh, Hops⟩
  iunfold memW
  rw [hv]
  iframe Hops Hmc
  icases Hh with (Hh | Hh)
  · iunfold hookPost at Hh
    icases Hh with ⟨Ha, Hs⟩
    iexists _, _; iunfold hookPre; iframe; ipureintro
    exact ⟨Int.le_refl _, by omega, by omega⟩
  · iexists _, _; iframe; ipureintro; exact ⟨by omega, by omega⟩

/-- **`end`'s history part from the operation's** (the follower's lower bound at the next count is
the history after the revision). -/
theorem leadPre_end (γh : HistNames) (ks : List GoString) (ops : List OpM) (n : Nat) (lead : Bool)
    (P : PendM) (hh : histAt ks ops (n + 1) = histAfter (histAt ks ops n) P) :
    leadPre (GF := GF) γh ks ops n lead ⊢
      if lead then histW γh (histAt ks ops n) (compsAt ks ops n)
      else monoListLbOwn γh.l (histAfter (histAt ks ops n) P) := by
  unfold leadPre
  cases lead
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hh]
  · simp only [↓reduceIte]; iintro H; iexact H

/-- **The operation's history part back from `end`'s.** -/
theorem leadPost_end (γh : HistNames) (ks : List GoString) (ops : List OpM) (n : Nat) (lead : Bool)
    (P : PendM) (hh : histAt ks ops (n + 1) = histAfter (histAt ks ops n) P)
    (hc : compsAt ks ops (n + 1) = compsAt ks ops n) :
    (if lead then histW (GF := GF) γh (histAfter (histAt ks ops n) P) (compsAt ks ops n)
      else iprop(True)) ⊢ leadPost γh ks ops n lead := by
  unfold leadPost
  cases lead
  · simp only [Bool.false_eq_true, ↓reduceIte]; iintro -; itrivial
  · simp only [↓reduceIte]; rw [hh, hc]

end lemmas

end mvccfull
end EtcdGrove
end Perennial
