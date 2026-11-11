/-
The writer's `txn` (lemmas). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.StepModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriteSubLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- A transaction's model step changes neither the compaction revision nor the leases. -/
theorem txn_fields (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o) (hk : o.kind = kTxn) :
    cmpAfter ks ops (n + 1) = cmpAfter ks ops n ∧ leasesAfter ks ops (n + 1) = leasesAfter ks ops n ∧
      grantedAfter ks ops (n + 1) = grantedAfter ks ops n ∧
      compsAt ks ops (n + 1) = compsAt ks ops n := by
  have hs := runM_succ ks ops n o ho
  have hc : ¬ o.kind = kCompact := by rw [hk]; decide
  have hg : ¬ o.kind = kGrant := by rw [hk]; decide
  have hr : ¬ o.kind = kRevoke := by rw [hk]; decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cmpAfter; rw [hs]; unfold opStep; simp [hk]
  · unfold leasesAfter; rw [hs]; unfold opStep; simp [hk]
  · unfold grantedAfter; rw [hs]; unfold opStep; simp [hk]
  · unfold compsAt; rw [hs]; unfold opStep; simp [hk]

theorem commitSt_nil (σ : MvccState) (hpn : σ.pending = none) : commitSt σ [] = σ := by
  cases σ with
  | mk log crev pending =>
    simp only at hpn; subst hpn
    unfold commitSt MvccState.commitPending MvccState.notify commitLog; simp

/-- The transaction's starting model. -/
abbrev txnP0 (Hs : List HRev) : PendM := ⟨W64 (Hs.length : Int), lastSt Hs, []⟩

theorem txn_opPend (ks : List GoString) (s : MSt) (o : OpM) (hk : o.kind = kTxn) :
    opPend ks s o = if o.write then o.subs.foldl (subStep ks) (txnP0 s.hs) else txnP0 s.hs := by
  have h0 : ¬ o.kind = kPut := by rw [hk]; decide
  have h1 : ¬ o.kind = kDelete := by rw [hk]; decide
  unfold opPend; rw [hk]; simp only [show ¬ (kTxn = kPut) by decide, show ¬ (kTxn = kDelete) by decide,
    ↓reduceIte, txnP0]

/-- **The member's state matches its history's last state** (nothing pending: the empty
transaction's model). -/
theorem txn_pendOk0 (ks : List GoString) (σ : MvccState) (Hs : List HRev)
    (hlen : Hs.length = σ.log.length) (h1 : 1 ≤ σ.log.length) (hrev : HistRevs ks σ.log Hs) :
    pendOk ks σ Hs [] (txnP0 Hs) := by
  refine ⟨rfl, ?_⟩
  obtain ⟨e, he, hok, -⟩ := hrev (Hs.length - 1) (by omega)
  have hl : lastSt Hs = e.1 := lastSt_of he
  show stMatch ks (lastSt Hs) (applyChanges _ (stateAfter σ.log) [])
  simp only [applyChanges, List.foldl_nil]
  rw [hl, ← stateAt_last σ.log h1, ← hlen]; exact hok

/-- The `j`-th sub-operation's step. -/
theorem foldl_take_succ (ks : List GoString) (subs : List SubM) (P0 : PendM) (j : Nat) (b : SubM)
    (hb : subs[j]? = some b) :
    (subs.take (j + 1)).foldl (subStep ks) P0 = subStep ks ((subs.take j).foldl (subStep ks) P0) b := by
  rw [List.take_add_one, hb]; simp

/-- **Each sub-operation is fresh against the changes before it** (`subsOk`, `Prov`). -/
theorem subFresh_of_prov (ks : List GoString) (L : List w64) (subs : List SubM) (j : Nat)
    (P : PendM) (b : SubM) (hs : subsOk ks L subs) (hp : Prov subs j P) (hb : subs[j]? = some b) :
    subFresh P.chs b := by
  refine ⟨fun hb0 c hc => ?_, fun hb1 c hc hd => ?_⟩
  · obtain ⟨i, hi, a, ha, h⟩ := hp c hc
    obtain ⟨h00, h10, -⟩ := hs.2 i j a b hi ha hb
    rcases h with ⟨-, ha0, hkey⟩ | ⟨-, ha1, hin⟩
    · rw [← hkey]; exact h00 ha0 hb0
    · intro heq; have := h10 ha1 hb0; rw [← heq, hin] at this; exact Bool.noConfusion this
  · obtain ⟨i, hi, a, ha, h⟩ := hp c hc
    obtain ⟨-, -, h01⟩ := hs.2 i j a b hi ha hb
    rcases h with ⟨-, ha0, hkey⟩ | ⟨hdel, -, -⟩
    · rw [← hkey]; exact h01 ha0 hb1
    · rw [hd] at hdel; exact Bool.noConfusion hdel

/-- A good pending model changes at most every key once. -/
theorem pgood_len (ks : List GoString) (M : GMap GoString kvRec) (rev : w64) (P : PendM)
    (hks : ks.Nodup) (hg : PGood ks M rev P) : P.chs.length ≤ ks.length := by
  have hnd := (hg.2.2 hks).1
  have hsub : ∀ x ∈ P.chs.map change.key', x ∈ ks := by
    intro x hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx; exact hg.2.1 c hc
  have := List.Nodup.length_le_of_subset hnd hsub
  simpa using this

end model

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem txn_zip_disc (ms : List GoMap) (Hs : List HRev) :
    ms.zip ((Hs.map Prod.fst).zip (List.replicate Hs.length DFrac.discard)) =
      (ms.zip Hs).map (fun x => (x.1, (x.2.1, DFrac.discard))) := by
  induction ms generalizing Hs with
  | nil => simp
  | cons m ms ih =>
    cases Hs with
    | nil => simp
    | cons e Hs => simp [List.replicate_succ, ih]

theorem txn_statesAt_hist (ms : List GoMap) (Hs : List HRev) :
    statesP (GF := GF) ms Hs ⊢ statesAt ms (Hs.map Prod.fst) (List.replicate Hs.length DFrac.discard) := by
  unfold statesP statesAt
  iintro ⟨%h, H⟩
  rw [txn_zip_disc, BigSepL.bigSepL_map]
  isplitr
  · ipureintro; simp [h]
  iexact H

theorem leadPre_lb (γh : HistNames) (ks : List GoString) (ops : List OpM) (n : Nat) (lead : Bool) :
    leadPre (GF := GF) γh ks ops n lead ⊢ leadPre γh ks ops n lead ∗ monoListLbOwn γh.l (histAt ks ops n) := by
  unfold leadPre
  cases lead
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro #H
    iframe #
    iapply monoListLbOwn_le _ (runM_hs_prefix ks ops n (n + 1) (by omega))
    iexact H
  · simp only [↓reduceIte]
    iintro H
    iapply histW_lb; iexact H

end own

section model2
variable [GooseExts]

/-- The history's states match the store's at every revision of the member's log. -/
theorem txn_hist_match (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (hok : logOk ks ops) (n : Nat) (hn : n ≤ ops.length) (Hs' : List HRev)
    (hp : histAt ks ops n <+: Hs') :
    ∀ r : Nat, r < (σOf ks ops n).log.length →
      ∃ M, (Hs'.map Prod.fst)[r]? = some M ∧ stMatch ks M (stateAt (σOf ks ops n).log r) := by
  intro r hr
  obtain ⟨-, ⟨-, hH⟩, -⟩ := logOk_hist ks hks ops hok n n (Nat.le_refl _) hn
  rw [σOf_notified] at hH
  obtain ⟨e, he, hrev⟩ := hH r hr
  obtain ⟨t, rfl⟩ := hp
  have hlt : r < (histAt ks ops n).length := by
    have := List.getElem?_eq_some_iff.1 he; exact this.1
  refine ⟨e.1, ?_, hrev.1⟩
  rw [List.getElem?_map, List.getElem?_append_left hlt, he]; rfl

theorem logWf'_append_nil {log : Log} (h : LogWf' log) (hne : log ≠ []) : LogWf' (log ++ [[]]) := by
  refine ⟨fun _ => ?_, fun r cs i k hr hi => ?_⟩
  · rw [List.getElem?_append_left (List.length_pos_iff.2 hne)]; exact h.1 hne
  · by_cases hlt : r < log.length
    · rw [List.getElem?_append_left hlt] at hr
      have := h.2 r cs i k hr hi
      rw [stateAt_append_lt _ _ (by omega)]
      exact this
    · rw [List.getElem?_append_right (by omega)] at hr
      have : r - log.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 hr).1
        simp at this; omega
      rw [this] at hr
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      simp at hi

/-- **Every change of the log is of a key of the tester's.** -/
theorem logKeys (ks : List GoString) (ops : List OpM) (h : logOk ks ops) :
    ∀ n, ∀ cs ∈ logOfHist (histAt ks ops n), ∀ c ∈ cs, c.key ∈ ks := by
  intro n
  induction n with
  | zero =>
    intro cs hcs c hc
    have : logOfHist (histAt ks ops 0) = [[], []] := by
      unfold histAt; rw [runM_zero]; rfl
    rw [this] at hcs
    simp at hcs; subst hcs; simp at hc
  | succ n ih =>
    cases hn : ops[n]? with
    | none =>
      have : runM ks ops (n + 1) = runM ks ops n := by
        unfold runM; rw [List.take_add_one, hn]; simp
      unfold histAt at ih ⊢; rw [this]; exact ih
    | some o =>
      have hs := runM_succ ks ops n o hn
      have hI := runM_inv ks ops h n
      obtain ⟨hpre, -, hmatch, hlo, -⟩ := hI
      have hlen : 2 ≤ (runM ks ops n).hs.length := by
        have := hpre.length_le; simp [hist0] at this; omega
      obtain ⟨eL, heL⟩ : ∃ e, (runM ks ops n).hs[(runM ks ops n).hs.length - 1]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hM := hmatch _ _ heL
      rw [← lastSt_of heL] at hM
      have hdom : ∀ k, (lastSt (runM ks ops n).hs !! k).isSome → k ∈ ks := by
        intro k hk
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
        have hf := hM.1 k
        rw [hx] at hf
        have hm := List.mem_of_find?_eq_some hf
        have hkk : (kvOfRec k x).key = k := rfl
        have := hM.2 _ hm
        rwa [hkk] at this
      obtain ⟨hg, -⟩ := opPend_good ks (runM ks ops n) o (h n o hn) hdom hlo.2.2.2
      intro cs hcs c hc
      have hh : histAt ks ops (n + 1) = histAfter (histAt ks ops n) (opPend ks (runM ks ops n) o) := by
        unfold histAt; rw [hs]; rfl
      rw [hh, logOfHist_histAfter] at hcs
      unfold commitLog at hcs
      split at hcs
      · exact ih cs hcs c hc
      · simp only [List.mem_append, List.mem_singleton] at hcs
        rcases hcs with h1 | h1
        · exact ih cs h1 c hc
        · subst h1
          obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
          rw [toChange_key]; exact hg.2.1 c' hc'

/-- **The read log of a write transaction without changes is well formed** (`writeRange`'s and
`writeSub`'s `LogOk`): each revision changes each key of the tester's at most once. -/
theorem txn_logOk0 (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (h : logOk ks ops) (n : Nat) (hkl : ks.length < 2 ^ 63)
    (hl : (σOf ks ops n).log.length < 2 ^ 62) :
    txn.LogOk ((σOf ks ops n).log ++ [[]]) := by
  have hnd := nodup_of_sorted hks
  have hI := (runM_inv ks ops h n).2.2.2.2 hnd
  have hwf : LogWf (σOf ks ops n).log := hI.2.1
  have hne : (σOf ks ops n).log ≠ [] := by
    have h2 := (runM_hs_len ks ops n).1
    have : (σOf ks ops n).log.length = (runM ks ops n).hs.length := by simp [σOf, logOfHist, histAt]
    intro h0; rw [h0] at this; simp at this; omega
  have hcs : ∀ cs ∈ (σOf ks ops n).log, cs.length < 2 ^ 63 := by
    intro cs hc
    obtain ⟨r, hr⟩ := List.mem_iff_getElem?.1 hc
    have hon := hI.1 r
    have hg : (logOfHist (histAt ks ops n)).getD r [] = cs := by
      rw [List.getD_eq_getElem?_getD]; show ((σOf ks ops n).log[r]?).getD [] = cs; rw [hr]; rfl
    rw [hg] at hon
    have hsub : ∀ x ∈ cs.map Change.key, x ∈ ks := by
      intro x hx
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hx
      exact logKeys ks ops h n cs hc c hc'
    have := List.Nodup.length_le_of_subset hon hsub
    simp at this; omega
  refine txn.LogOk.of_cert ⟨logWf'_append_nil (LogWf'.of_wf hwf) hne, by simp; omega, ?_⟩ (by simp)
  intro cs hc
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with h1 | h1
  · exact hcs cs h1
  · subst h1; simp

/-- **The write transaction's `j`-th sub-operation's premises** (`writeSub`'s): its freshness
against the changes before it, its put's key and lease, and the changes so far at most one per
key. -/
theorem txn_sub_facts (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (h : logOk ks ops) (n : Nat) (o : OpM) (ho : ops[n]? = some o) (hk : o.kind = kTxn)
    (hw : o.write = true) (j : Nat) (b : SubM) (hb : o.subs[j]? = some b) :
    let Pj := (o.subs.take j).foldl (subStep ks) (txnP0 (histAt ks ops n))
    subFresh Pj.chs b ∧ (b.kind = W64 0 → b.key ∈ ks ∧ (b.lease = W64 0 ∨ b.lease ∈ leasesAfter ks ops n)) ∧
      Pj.chs.length ≤ ks.length := by
  intro Pj
  have hv := h n o ho
  have hs : subsOk ks (runM ks ops n).leases o.subs := hv.2.2.2.1 hk hw
  have hI := runM_inv ks ops h n
  have hl : LeaseSt (runM ks ops n).leases (lastSt (runM ks ops n).hs) := hI.2.2.2.1.2.2.2
  obtain ⟨hg, -, hp⟩ := txn_good ks (lastSt (runM ks ops n).hs) (W64 ((runM ks ops n).hs.length : Int))
    (runM ks ops n).leases o.subs hs hl j
  refine ⟨subFresh_of_prov ks _ o.subs j _ b hs hp hb, fun h0 => hs.1 b (List.mem_of_getElem? hb) h0,
    pgood_len ks _ _ _ (nodup_of_sorted hks) hg⟩

end model2

end mvccfull
end EtcdGrove
end Perennial
