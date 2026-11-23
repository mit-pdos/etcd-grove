/-
Package `proxy`: helpers of the decision handlers (`handleProposeResponse`,
`handleRecorderResponse`): `hasSameBatches`, `decidedTheProposedValue`, `getHighestIndex`,
`updateEpochTime` (leader mode 1: nothing), and the log's updates (`rd_log_acc`: one slot
replaced, `rd_log_snoc`: an empty slot appended; `rd_smrP_set`, `rd_smrP_snoc`).
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

/-- An ASCII string is valid UTF-8. -/
theorem rd_ascii_strOk (s : GoString) (h : msg.asciiOk s) : msg.strOk s := by
  unfold msg.strOk
  induction s with
  | nil => rfl
  | cons c rest ih =>
    have hc : c.toNat < 128 := h c (by simp)
    have hr : msg.asciiOk rest := fun b hb => h b (by simp [hb])
    unfold msg.validUtf8
    simp only [show c.toNat < 0x80 from hc, ↓reduceIte]
    exact ih hr

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

/-! ## The log -/

/-- Slot `idx` of the log, out for a replacement. -/
theorem rd_log_acc (γ : QNames) (γs : GName) (cf : QConf) (slots : List Slot) (L : List (Option (List GoString)))
    (idx : Nat) (s : Slot) (hs : slots[idx]? = some s) :
    ⊢@{IProp GF} logP γ γs cf slots L -∗ ∃ o, ⌜L[idx]? = some o⌝ ∗ slotP γ γs cf idx s o ∗
      ∀ s' o', slotP γ γs cf idx s' o' -∗ logP γ γs cf (slots.set idx s') (L.set idx o') := by
  iintro Hlog
  iunfold logP at Hlog
  icases Hlog with ⟨%Hlen, Hlog⟩
  icases (BigSepL.bigSepL_delete_cond hs).1 $$ Hlog with ⟨⟨%o, %Ho, Hs⟩, Hrest⟩
  iexists o
  iframe Hs
  isplitr
  · ipureintro; exact Ho
  iintro %s' %o' Hs'
  ihave Hrest := BigSepL.bigSepL_impl (Ψ := fun k y => if k = idx then iprop(emp) else
      iprop(∃ o, ⌜(L.set idx o')[k]? = some o⌝ ∗ slotP (GF := GF) γ γs cf k y o)) $$ Hrest
  ihave Hrest := Hrest $$ []
  · imodintro
    iintro %k %y %_ H
    by_cases hk : k = idx
    · simp only [hk, ↓reduceIte]; iexact H
    · simp only [hk, ↓reduceIte]
      icases H with ⟨%o2, %Ho2, H⟩
      iexists o2
      iframe H
      ipureintro
      rw [List.getElem?_set_ne (Ne.symm hk)]; exact Ho2
  icases (BigSepL.bigSepL_insert_acc hs) $$ Hrest with ⟨-, Hw⟩
  ihave Hrest := Hw $$ %s' []
  · simp only [↓reduceIte]; iempintro
  have hs' : (slots.set idx s')[idx]? = some s' := by
    rw [List.getElem?_set_self]; exact (List.getElem?_eq_some_iff.1 hs).1
  iunfold logP
  isplitr
  · ipureintro; simp [Hlen]
  iapply (BigSepL.bigSepL_delete_cond hs').2
  isplitl [Hs']
  · iexists o'
    iframe Hs'
    ipureintro
    rw [List.getElem?_set_self]; rw [← Hlen]; exact (List.getElem?_eq_some_iff.1 hs).1
  iexact Hrest

/-- An empty slot (`Slot{}` with nil slices). -/
def rd_emptySlot : Slot := ⟨slice.nil, slice.nil, false, false, W32 0, W64 0⟩

theorem rd_log_snoc (γ : QNames) (γs : GName) (cf : QConf) (slots : List Slot) (L : List (Option (List GoString)))
    (e : Slot) (he : e.decided' = false ∧ e.proposedBatch' = slice.nil) :
    ⊢@{IProp GF} logP γ γs cf slots L -∗ logP γ γs cf (slots ++ [e]) (L ++ [none]) := by
  iintro Hlog
  iunfold logP at Hlog
  icases Hlog with ⟨%Hlen, Hlog⟩
  iunfold logP
  isplitr
  · ipureintro; simp [Hlen]
  iapply BigSepL.bigSepL_snoc.2
  isplitl [Hlog]
  · iapply BigSepL.bigSepL_impl $$ Hlog
    imodintro
    iintro %k %y %Hk ⟨%o, %Ho, H⟩
    iexists o
    iframe H
    ipureintro
    rw [List.getElem?_append_left (by rw [← Hlen]; exact (List.getElem?_eq_some_iff.1 Hk).1)]
    exact Ho
  iexists none
  isplitr
  · ipureintro; rw [Hlen]; simp
  iunfold slotP
  isplitr
  · ipureintro; simp [he.1]
  iexists []
  rw [he.2]
  isplitl []
  · iapply ownSlice_nil
  by_cases h : sumSlot cf.n cf.ep (slots.length : Nat)
  · rw [decide_eq_true h]; simp only [↓reduceIte]; itrivial
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ↓reduceIte]
    iapply BigSepL.bigSepL_nil.2; iempintro

theorem rd_smrP_set (γ : QNames) (pr bm ebm : Loc) (L : List (Option (List GoString))) (c : w64)
    (D : List (List GoString)) (Bm : GMap GoString Batch) (idx : Nat) (o : Option (List GoString))
    (hidx : L[idx]? = some none) (h1 : 1 ≤ idx) :
    ⊢@{IProp GF} smrP γ pr bm ebm L c D Bm -∗ smrP γ pr bm ebm (L.set idx o) c D Bm := by
  iintro H
  iunfold smrP at H
  icases H with ⟨%E, %t, Hc, Ht, %Hp, #Hlb, Hkv, Hm, %HE, #Hknown, %Hp2⟩
  iunfold smrP
  iexists E, t
  iframe Hc Ht Hkv Hm Hlb Hknown
  ipureintro
  refine ⟨⟨Hp.1, by simpa using Hp.2.1, by simpa using Hp.2.2.1, ?_⟩, HE, Hp2⟩
  intro i hi
  have hne : i + 1 ≠ idx := by
    intro h; subst h; rw [Hp.2.2.2 i hi] at hidx; simp at hidx
  rw [List.getElem?_set_ne (Ne.symm hne)]; exact Hp.2.2.2 i hi

theorem rd_smrP_snoc (γ : QNames) (pr bm ebm : Loc) (L : List (Option (List GoString))) (c : w64)
    (D : List (List GoString)) (Bm : GMap GoString Batch) (h73 : L.length + 1 ≤ 601) :
    ⊢@{IProp GF} smrP γ pr bm ebm L c D Bm -∗ smrP γ pr bm ebm (L ++ [none]) c D Bm := by
  iintro H
  iunfold smrP at H
  icases H with ⟨%E, %t, Hc, Ht, %Hp, #Hlb, Hkv, Hm, %HE, #Hknown, %Hp2⟩
  iunfold smrP
  iexists E, t
  iframe Hc Ht Hkv Hm Hlb Hknown
  ipureintro
  refine ⟨⟨Hp.1, by simp; omega, by simpa using h73, ?_⟩, HE, Hp2⟩
  intro i hi
  rw [List.getElem?_append_left (by have := Hp.2.1; omega)]; exact Hp.2.2.2 i hi

end proofs

end Perennial.raxos
