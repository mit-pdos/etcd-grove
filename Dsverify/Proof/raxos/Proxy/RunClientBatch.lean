/-
Package `proxy`: `handleClientBatch`'s lemmas (`RunClientBatch2.lean` has its proof): the bound
of the leader's wait, the pending slots and the timers after issuing a slot, the reads of the log
and of the committed index.
-/
module

public import Dsverify.Proof.raxos.Proxy.RunDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

instance rc_notInterface_int64 : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

theorem rc_msWait_nonneg (p c : w64) (t r : Nat) (ht : t ≤ 40000) (hr : r ≤ 4)
    (h1 : 0 ≤ sint.Z c) (h2 : sint.Z p ≤ 601) (h3 : sint.Z c < sint.Z p) :
    0 ≤ sint.Z (W64 ((t : Int) * (r : Int)) * (p - c)) := by
  have hpc : sint.Z (p - c) = sint.Z p - sint.Z c := by word
  have htr : (t : Int) * r ≤ 160000 := by
    have := Int.mul_le_mul (a := (t : Int)) (b := (r : Int)) (c := 40000) (d := 4) (by omega)
      (by omega) (by omega) (by omega)
    omega
  have htr0 : 0 ≤ (t : Int) * r := Int.mul_nonneg (by omega) (by omega)
  have hw : sint.Z (W64 ((t : Int) * (r : Int))) = (t : Int) * r := by
    generalize (t : Int) * r = m at *; word
  rw [w64_mul_toInt _ _ (by rw [hw]; omega) (by rw [hpc]; omega), hw, hpc]
  exact Int.mul_nonneg htr0 (by omega)

/-- The pending slots and the timers after issuing slot `p` (the new frontier). -/
theorem rc_issue_pure (Pm : GMap Int Unit) (ts : List Loc) (tm : Loc) (lp p : Int) (n : Nat)
    (HPm : (∀ i, (Pm !! i).isSome = true → 1 ≤ i ∧ i ≤ lp) ∧
      ∀ i, 1 ≤ i → i ≤ lp → i < n ∨ (Pm !! i).isSome = true)
    (Hts : ts.length = 1000000 ∧ ∀ (i : Nat) (t : Loc), ts[i]? = some t → t ≠ null → (i : Int) ≤ lp)
    (h0 : 0 ≤ lp) (h1 : lp + 1 ≤ p) (h2 : p = lp + 1 ∨ p ≤ n) :
    ((∀ i, ((Pm.insert p ()) !! i).isSome = true → 1 ≤ i ∧ i ≤ p) ∧
      ∀ i, 1 ≤ i → i ≤ p → i < n ∨ ((Pm.insert p ()) !! i).isSome = true) ∧
    ((ts.set p.toNat tm).length = 1000000 ∧
      ∀ (i : Nat) (t : Loc), (ts.set p.toNat tm)[i]? = some t → t ≠ null → (i : Int) ≤ p) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    by_cases hip : p = i
    · subst hip; have := HPm.1; omega
    · have hi' : (Pm !! i).isSome = true := by
        have : (Pm.insert p ()) !! i = Pm !! i := GMap.lookup_insert_ne Pm () hip
        rw [← this]; exact hi
      have := HPm.1 i hi'; omega
  · intro i hi1 hi2
    by_cases hip : p = i
    · right; subst hip; rw [show (Pm.insert p ()) !! p = some () from GMap.lookup_insert Pm p ()]; rfl
    · have heq : (Pm.insert p ()) !! i = Pm !! i := GMap.lookup_insert_ne Pm () hip
      rw [heq]
      by_cases hil : i ≤ lp
      · exact HPm.2 i hi1 hil
      · left; omega
  · simp [Hts.1]
  · intro i t h hn
    by_cases hi : i = p.toNat
    · omega
    · rw [List.getElem?_set_ne (Ne.symm hi)] at h
      have := Hts.2 i t h hn; omega

/-- `smrP`'s committed index, for a read. -/
theorem rc_smrP_c_acc (γ : QNames) (pr bm ebm : Loc) (L : List (Option (List GoString))) (c : w64)
    (D : List (List GoString)) (Bm : GMap GoString Batch) :
    ⊢@{IProp GF} smrP γ pr bm ebm L c D Bm -∗
      pr.[Proxy, go!"committedIndex"] ↦ c ∗
      ⌜sint.Z c = D.length ∧ D.length < L.length ∧ L.length ≤ 601 ∧
        ∀ i (h : i < D.length), L[i + 1]? = some (some D[i])⌝ ∗
      (pr.[Proxy, go!"committedIndex"] ↦ c -∗ smrP γ pr bm ebm L c D Bm) := by
  iintro Hsmr
  iunfold smrP at Hsmr
  icases Hsmr with ⟨%E, %t, Hc, Ht, %Hp, #Hlb, Hkv, Hm, %HE, #Hknown, %Hp2⟩
  iframe Hc
  isplitr
  · ipureintro; exact Hp
  iintro Hc
  iunfold smrP
  iexists E, t
  iframe Hc Ht Hkv Hm Hlb Hknown
  ipureintro; exact ⟨Hp, HE, Hp2⟩

instance rc_decided_persistent (γ : QNames) (i : Int) (ids : List GoString) :
    Persistent (decided (GF := GF) γ i ids) := by
  unfold decided evIn; infer_instance

/-- Slot `p` of the log: its decision `o` (its `decided` flag), and, decided, its `decided`
fact. -/
theorem rc_log_slot (γ : QNames) (γs : GName) (cf : QConf) (slots : List Slot) (L : List (Option (List GoString)))
    (p : Nat) (s : Slot) (hs : slots[p]? = some s) :
    ⊢@{IProp GF} logP γ γs cf slots L -∗ ∃ o, ⌜L[p]? = some o ∧ s.decided' = o.isSome⌝ ∗
      □ (∀ ids, ⌜o = some ids ∧ p ≠ 0⌝ -∗ decided γ p ids) ∗ logP γ γs cf slots L := by
  iintro Hlog
  iunfold logP at Hlog
  icases Hlog with ⟨%Hlen, Hlog⟩
  icases (BigSepL.bigSepL_lookup_acc hs).1 $$ Hlog with ⟨⟨%o, %Ho, Hslot⟩, Hclose⟩
  iunfold slotP at Hslot
  icases Hslot with ⟨%Hdec, Hrest⟩
  rcases o with _ | ids
  · iexists none
    isplitr
    · ipureintro; exact ⟨Ho, Hdec⟩
    isplitr
    · imodintro; iintro %ids ⟨%h, -⟩; cases h
    ihave Hlog := Hclose $$ %s [Hrest]
    · iexists none; isplitr
      · ipureintro; exact Ho
      iunfold slotP; isplitr
      · ipureintro; exact Hdec
      iexact Hrest
    rw [list_set_lookup_self _ _ _ hs]
    iunfold logP; iframe Hlog; ipureintro; exact Hlen
  · icases Hrest with ⟨#Hids, %Hok, #Hd⟩
    iexists some ids
    isplitr
    · ipureintro; exact ⟨Ho, Hdec⟩
    isplitr
    · imodintro; iintro %ids' ⟨%h, %hp⟩
      cases h
      simp only [hp, ↓reduceIte]
      iexact Hd
    ihave Hlog := Hclose $$ %s []
    · iexists some ids; isplitr
      · ipureintro; exact Ho
      iunfold slotP; isplitr
      · ipureintro; exact Hdec
      dsimp only
      iframe #; ipureintro; exact Hok
    rw [list_set_lookup_self _ _ _ hs]
    iunfold logP; iframe Hlog; ipureintro; exact Hlen

theorem rc_log_len (γ : QNames) (γs : GName) (cf : QConf) (slots : List Slot)
    (L : List (Option (List GoString))) :
    logP (GF := GF) γ γs cf slots L ⊢ ⌜slots.length = L.length⌝ := by
  iintro Hlog
  iunfold logP at Hlog
  icases Hlog with ⟨%H, -⟩
  ipureintro; exact H

/-- `issue_ghost`, at mask `⊤`, in this section's context. -/
theorem rc_issue (γ : QNames) (k : Int) (n p : Int) (t : Ticket) (ids : List GoString) (hnp : n ≤ p) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ spentLb γ 0 -∗ initFront γ k n -∗ credit γ t -∗
      (⌜p = n⌝ ∨ decided γ (p - 1) ids) ={⊤}=∗
      initFront γ k (p + 1) ∗ initTok γ k p ∗ ⌜1 ≤ p ∧ p ≤ 600⌝ := by
  iintro #Hc #Hs Hf Hcr Hd
  iapply (issue_ghost γ ⊤ CoPset.subseteq_top k n p t ids hnp) $$ Hc Hs Hf Hcr Hd

end proofs

end Perennial.raxos
