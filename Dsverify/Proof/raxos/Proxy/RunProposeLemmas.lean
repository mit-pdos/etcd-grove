/-
Package `proxy`: helper lemmas of `proposeToIndex`'s proof (`RunPropose.lean`).

`proposeToIndex` (`proxyclienthandler.go`): a timer's request to propose a
pending slot `i` (its ghost element `reqIdxP`): the slot's init token is taken from the pending
map; if the slot is decided already, nothing; else a batch of `toBeProposed` (or `"nil"`) is
proposed with `cons_init`, the log is extended to the slot, which records the proposed ids.
-/
module

public import Dsverify.Proof.raxos.Proxy.RunDefs
public import Dsverify.Proof.raxos.Proxy.MabLeader

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

instance rp_idP_persistent (γ : QNames) (γs : GName) (x : GoString) :
    Persistent (idP (GF := GF) γ γs x) := by
  unfold idP; infer_instance

instance rp_decidedSlotsP_persistent (γ : QNames) (a b c : GoSlice) :
    Persistent (decidedSlotsP (GF := GF) γ a b c) := by
  unfold decidedSlotsP; infer_instance

instance rp_batchesP_persistent (γ : QNames) (vs : List raxos.proto.client.ClientBatch)
    (bs : List Batch) : Persistent (batchesP (GF := GF) γ vs bs) := by
  unfold batchesP; infer_instance

theorem rp_bigSepL_take_drop {A : Type} (n : Nat) (l : List A) (Φ : A → IProp GF) :
    ([∗list] x ∈ l, Φ x) ⊢ ([∗list] x ∈ l.take n, Φ x) ∗ ([∗list] x ∈ l.drop n, Φ x) := by
  conv => lhs; rw [← List.take_append_drop n l]
  exact BigSepL.bigSepL_append.1

theorem rp_batchesP_snoc (γ : QNames) (vs : List raxos.proto.client.ClientBatch)
    (bs : List Batch) (v : raxos.proto.client.ClientBatch) (b : Batch) (hb : batchFit b) :
    batchesP (GF := GF) γ vs bs ∗ repCBVal v .discard b ∗ batchReg γ b.id b ⊢
      batchesP γ (vs ++ [v]) (bs ++ [b]) := by
  iintro ⟨Hbs, #Hv, #Hreg⟩
  iunfold batchesP at Hbs
  icases Hbs with ⟨%Hlen, Hbs⟩
  iunfold batchesP
  isplitr
  · ipureintro
    refine ⟨by simp [Hlen.1], ?_⟩
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact Hlen.2 c hc
    · simp at hc; subst hc; exact hb
  iapply BigSepL.bigSepL_append.2
  isplitl [Hbs]
  · iapply BigSepL.bigSepL_impl $$ Hbs
    imodintro
    iintro %k %o %hk ⟨%b0, %Hb0, Hr⟩
    iexists b0
    iframe Hr
    ipureintro
    rw [List.getElem?_append_left (by rw [← Hlen.1]; exact (List.getElem?_eq_some_iff.1 hk).1)]
    exact Hb0
  iapply BigSepL.bigSepL_singleton.2
  iexists b
  iframe Hv Hreg
  ipureintro
  simp [Hlen.1]

theorem rs_sum_register (γ : QNames) (c : QConf) (p : List Nat) (hc : c.ok) (hp : isPerm c.n p) :
    ⊢@{IProp GF} inv smrN (smrInv γ) ={⊤}=∗
      batchReg γ (summaryId p) ⟨summaryId p, -1, [summaryId p]⟩ := by
  iintro #Hinv
  iapply (sum_register γ ⊤ CoPset.subseteq_top c p hc hp) $$ Hinv

theorem rs_cons_init (γ : QNames) (c : QConf) (me i : Int) (ids : List GoString) (lead : Bool)
    (hc : c.ok) (hids : ids ≠ []) (hsum : sumSlot c.n c.ep i → ∃ p, isPerm c.n p ∧ ids = [summaryId p]) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ confIs γ c -∗ initTok γ me i -∗
      (if lead then leadEv γ c i me else iprop(True)) -∗
      ([∗list] x ∈ ids, ∃ b, batchReg γ x b) ={⊤}=∗ evIn γ (.init i me ids lead) := by
  iintro #Hinv #Hc Htok Hl Hids
  iapply (cons_init γ ⊤ CoPset.subseteq_top c me i ids lead hc hids hsum) $$ Hinv Hc Htok Hl Hids

/-- The leader flag: the wait is zero exactly when the replica is first in the order. -/
theorem rp_flag (c : QConf) (k : Nat) (q : List Nat) (hc : c.ok) (hk : 1 ≤ k ∧ k ≤ c.n)
    (hq : isPerm c.n q) :
    (W64 ((c.tmo : Int) * (q.idxOf k : Int)) = W64 0) ↔ q.head? = some k := by
  have hkq : k ∈ q := (isPerm_mem c.n q hq k).2 hk
  have hidx : q.idxOf k < q.length := List.idxOf_lt_length_of_mem hkq
  have hl := isPerm_length c.n q hq
  unfold QConf.ok at hc
  rw [← idxOf_zero k q hkq]
  have hb : (c.tmo : Int) * (q.idxOf k : Int) ≤ 200000 := by
    have := Int.mul_le_mul (a := (c.tmo : Int)) (b := (q.idxOf k : Int)) (c := 40000) (d := 5)
      (by omega) (by omega) (by omega) (by omega)
    omega
  have hb0 : 0 ≤ (c.tmo : Int) * (q.idxOf k : Int) := Int.mul_nonneg (by omega) (by omega)
  constructor
  · intro h
    have h1 : sint.Z (W64 ((c.tmo : Int) * (q.idxOf k : Int))) = (c.tmo : Int) * (q.idxOf k : Int) := by
      generalize (c.tmo : Int) * (q.idxOf k : Int) = m at *; word
    rw [h] at h1
    have : (c.tmo : Int) * (q.idxOf k : Int) = 0 := by rw [← h1]; rfl
    rcases Int.mul_eq_zero.1 this with h | h <;> omega
  · intro h; rw [h]; simp

/-- The log's new slot (`Slot{}` but for its fields set to their zero values). -/
abbrev rp_s0 : Slot := ⟨slice.nil, slice.nil, false, false, W32 0, W64 0⟩

theorem rp_log_len (γ : QNames) (γs : GName) (cf : QConf) (slots : List Slot)
    (L : List (Option (List GoString))) :
    logP (GF := GF) γ γs cf slots L ⊢ ⌜slots.length = L.length⌝ := by
  iintro Hlog
  iunfold logP at Hlog
  icases Hlog with ⟨%H, -⟩
  ipureintro; exact H

/-- A new slot of the log, not proposed here. -/
theorem rp_slotP_s0 (γ : QNames) (γs : GName) (c : QConf) (j : Nat) :
    ⊢@{IProp GF} slotP γ γs c j rp_s0 none := by
  iunfold slotP
  isplitr
  · ipureintro; rfl
  iexists []
  isplitr
  · iapply (ownSlice_nil (V := GoString) DFrac.discard)
  by_cases h : sumSlot c.n c.ep j
  · rw [decide_eq_true h]; simp only [↓reduceIte]; itrivial
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ↓reduceIte]
    iapply BigSepL.bigSepL_nil.2; iempintro

theorem rp_slot_undecided (slots : List Slot) (m n : Nat) (sx : Slot)
    (h : (slots ++ List.replicate m rp_s0)[n]? = some sx)
    (hnd : ¬ (n < slots.length ∧ ∃ s, slots[n]? = some s ∧ s.decided' = true)) :
    sx.decided' = false := by
  by_cases hn : n < slots.length
  · rw [List.getElem?_append_left hn] at h
    cases hd : sx.decided'
    · rfl
    · exact absurd ⟨hn, sx, h, hd⟩ hnd
  · rw [List.getElem?_append_right (by omega)] at h
    have := List.mem_of_getElem? h
    simp at this; rw [this.2]

theorem rp_smrP_ext (γ : QNames) (pr bm ebm : Loc) (L : List (Option (List GoString)))
    (c : w64) (D : List (List GoString)) (Bm : GMap GoString Batch) (m : Nat)
    (h : m = 0 ∨ L.length + m ≤ 601) :
    smrP (GF := GF) γ pr bm ebm L c D Bm ⊢ smrP γ pr bm ebm (L ++ List.replicate m none) c D Bm := by
  iintro Hs
  iunfold smrP at Hs
  icases Hs with ⟨%E, %t, Hc, Ht, %Hp, Hrest⟩
  iunfold smrP
  iexists E, t
  iframe
  ipureintro
  refine ⟨Hp.1, by simp; omega, by simp; omega, ?_⟩
  intro j hj
  rw [List.getElem?_append_left (by omega)]
  exact Hp.2.2.2 j hj

theorem rp_ts_set (ts : List Loc) (lp : Int) (n : Nat)
    (h : ts.length = 1000000 ∧ ∀ (i : Nat) (t : Loc), ts[i]? = some t → t ≠ null → (i : Int) ≤ lp) :
    (ts.set n null).length = 1000000 ∧
      ∀ (i : Nat) (t : Loc), (ts.set n null)[i]? = some t → t ≠ null → (i : Int) ≤ lp := by
  refine ⟨by simp [h.1], ?_⟩
  intro j t hj ht
  rw [List.getElem?_set] at hj
  split at hj
  · split at hj
    · cases hj; exact absurd rfl ht
    · simp at hj
  · exact h.2 j t hj ht

theorem rp_nilBatch_ok' : batchOk nilBatch := by
  refine ⟨by simp only [i64Ok, nilBatch]; constructor <;> decide, by simp only [strOk, nilBatch]; rfl, by simp [nilBatch]⟩

theorem rp_nilBatch_ok : batchFit nilBatch := ⟨rp_nilBatch_ok', by decide +kernel⟩

theorem rp_pm_delete (Pm : GMap Int Unit) (lp : Int) (n n' : Nat) (i : Int)
    (h : (∀ j, (Pm !! j).isSome → 1 ≤ j ∧ j ≤ lp) ∧
      (∀ j, 1 ≤ j → j ≤ lp → j < n ∨ (Pm !! j).isSome))
    (hn : n ≤ n') (hi : i < n') :
    (∀ j, ((GMap.delete i Pm) !! j).isSome → 1 ≤ j ∧ j ≤ lp) ∧
      (∀ j, 1 ≤ j → j ≤ lp → j < n' ∨ ((GMap.delete i Pm) !! j).isSome) := by
  constructor
  · intro j hj
    by_cases hji : j = i
    · subst hji; simp [GMap.lookup_delete] at hj
    · rw [GMap.lookup_delete_ne _ (Ne.symm hji)] at hj; exact h.1 j hj
  · intro j h1 h2
    by_cases hji : j = i
    · subst hji; left; exact hi
    · rw [GMap.lookup_delete_ne _ (Ne.symm hji)]
      rcases h.2 j h1 h2 with h3 | h3
      · left; omega
      · right; exact h3

end proofs

end Perennial.raxos
