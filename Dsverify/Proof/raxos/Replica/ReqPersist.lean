/-
Package `replica`: a decoded request's representation made persistent (the recorder's handlers
read their requests only, and keep their slices: proposal ids in the slots, decided ids in the
decisions sent to the proxy, client batches in the store).
-/
module

public import Dsverify.Proof.raxos.Replica.RecDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section persist
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

theorem bigSepL_bupd' {A : Type} (Φ : Nat → A → IProp GF) (l : List A) :
    ([∗list] k ↦ x ∈ l, |==> Φ k x) ⊢ |==> [∗list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => iintro _; imodintro; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons x xs ih =>
    iintro H
    icases (BigSepL.bigSepL_cons (Φ := fun k x => iprop(|==> Φ k x))).1 $$ H with ⟨H0, Hs⟩
    imod H0 with H0
    imod ih (fun k y => Φ (k + 1) y) $$ Hs with Hs
    imodintro
    iapply (BigSepL.bigSepL_cons (Φ := Φ)).2
    iframe

theorem repList_persist {A : Type} (rep : Loc → DFrac → A → IProp GF) (ps : List Loc) (dq : DFrac)
    (xs : List A) (h : ∀ p x, rep p dq x ⊢ |==> rep p .discard x) :
    repList rep ps dq xs ⊢ |==> repList rep ps .discard xs := by
  unfold repList
  iintro ⟨%Hl, H⟩
  ihave H := BigSepL.bigSepL_mono (Ψ := fun i p => iprop(|==> ∃ x, ⌜xs[i]? = some x⌝ ∗
    rep p .discard x)) (fun {i p} _ => by
      iintro ⟨%x, %Hx, Hr⟩
      imod h p x $$ Hr with Hr
      imodintro; iexists x; iframe # ∗; ipureintro; exact Hx) $$ H
  imod bigSepL_bupd' _ _ $$ H with H
  imodintro
  iframe
  ipureintro; exact Hl

theorem repPMSingle_persist (l : Loc) (dq : DFrac) (m : GoString) :
    repPMSingle (GF := GF) l dq m ⊢ |==> repPMSingle l .discard m := by
  unfold repPMSingle
  iintro ⟨%x, Hx, %Hm⟩
  ipersist Hx
  imodintro; iexists x; iframe # ∗; ipureintro; exact Hm

theorem repPMBatch_persist (l : Loc) (dq : DFrac) (b : Batch) :
    repPMBatch (GF := GF) l dq b ⊢ |==> repPMBatch l .discard b := by
  unfold repPMBatch
  iintro ⟨%x, %ps, Hx, %Hu, %Hf, Hsl, Hl⟩
  ipersist Hx
  ipersist Hsl
  imod repList_persist _ _ _ _ (fun p x => repPMSingle_persist (GF := GF) p dq x) $$ Hl with Hl
  imodintro; iexists x, ps; iframe # ∗; ipureintro; exact ⟨Hu, Hf⟩

theorem repPMSlot_persist (l : Loc) (dq : DFrac) (d : DSlot) :
    repPMSlot (GF := GF) l dq d ⊢ |==> repPMSlot l .discard d := by
  unfold repPMSlot
  iintro ⟨%x, Hx, %Hu, %Hf, Hsl⟩
  ipersist Hx
  ipersist Hsl
  imodintro; iexists x; iframe # ∗; ipureintro; exact ⟨Hu, Hf⟩

theorem repProp_persist (l : Loc) (dq : DFrac) (p : Prop') :
    repProp (GF := GF) l dq p ⊢ |==> repProp l .discard p := by
  unfold repProp
  iintro ⟨%x, %bps, Hx, %Hu, %Hf, Hids, Hsl, Hl⟩
  ipersist Hx
  ipersist Hids
  ipersist Hsl
  imod repList_persist _ _ _ _ (fun p x => repPMBatch_persist (GF := GF) p dq x) $$ Hl with Hl
  imodintro; iexists x, bps; iframe # ∗; ipureintro; exact ⟨Hu, Hf⟩

theorem repPM_persist (l : Loc) (dq : DFrac) (m : PM) :
    repPM (GF := GF) l dq m ⊢ |==> repPM l .discard m := by
  unfold repPM
  iintro ⟨%x, %sps, Hx, %Hu, %Hf, Hp, Hsl, Hl⟩
  ipersist Hx
  ipersist Hsl
  imod repList_persist _ _ _ _ (fun p x => repPMSlot_persist (GF := GF) p dq x) $$ Hl with Hl
  cases hp : m.p with
  | none =>
    rw [hp] at *
    imodintro; iexists x, sps; iframe # ∗; ipureintro; exact ⟨Hu, Hf⟩
  | some p =>
    simp only [hp]
    imod repProp_persist _ _ _ $$ Hp with Hp
    imodintro; iexists x, sps; iframe # ∗; ipureintro; exact ⟨Hu, Hf⟩

theorem repDReq_persist (l : Loc) (dq : DFrac) (ids : List GoString) :
    repDReq (GF := GF) l dq ids ⊢ |==> repDReq l .discard ids := by
  unfold repDReq
  iintro ⟨%x, Hx, %Hu, Hsl⟩
  ipersist Hx
  ipersist Hsl
  imodintro; iexists x; iframe # ∗; ipureintro; exact Hu

theorem repDecSlot_persist (l : Loc) (dq : DFrac) (d : DSlot) :
    repDecSlot (GF := GF) l dq d ⊢ |==> repDecSlot l .discard d := by
  unfold repDecSlot
  iintro ⟨%x, Hx, %Hu, %Hf, Hsl⟩
  ipersist Hx
  ipersist Hsl
  imodintro; iexists x; iframe # ∗; ipureintro; exact ⟨Hu, Hf⟩

theorem repDecs_persist (l : Loc) (dq : DFrac) (ds : List DSlot) :
    repDecs (GF := GF) l dq ds ⊢ |==> repDecs l .discard ds := by
  unfold repDecs
  iintro ⟨%x, %ps, Hx, %Hu, Hsl, Hl⟩
  ipersist Hx
  ipersist Hsl
  imod repList_persist _ _ _ _ (fun p x => repDecSlot_persist (GF := GF) p dq x) $$ Hl with Hl
  imodintro; iexists x, ps; iframe # ∗; ipureintro; exact Hu

theorem repList_nil {A : Type} (rep : Loc → DFrac → A → IProp GF) (dq : DFrac) :
    ⊢ repList rep [] dq ([] : List A) := by
  unfold repList
  isplitr
  · ipureintro; rfl
  · iapply BigSepL.bigSepL_nil.2; iempintro

theorem repList_snoc {A : Type} (rep : Loc → DFrac → A → IProp GF) (qs : List Loc) (dq : DFrac)
    (xs : List A) (q : Loc) (x : A) :
    repList rep qs dq xs ∗ rep q dq x ⊢ repList rep (qs ++ [q]) dq (xs ++ [x]) := by
  unfold repList
  iintro ⟨⟨%Hl, Hs⟩, Hq⟩
  isplitr
  · ipureintro; simp [Hl]
  iapply (BigSepL.bigSepL_snoc (Φ := fun i p => iprop(∃ y, ⌜(xs ++ [x])[i]? = some y⌝ ∗
    rep p dq y))).2
  isplitl [Hs]
  · iapply BigSepL.bigSepL_mono (Φ := fun i p => iprop(∃ y, ⌜xs[i]? = some y⌝ ∗ rep p dq y))
      (fun {i p} hi => by
        iintro ⟨%y, %Hy, H⟩
        iexists y; iframe; ipureintro
        rw [List.getElem?_append_left (by
          have := (List.getElem?_eq_some_iff.1 Hy).1; exact this)]; exact Hy) $$ Hs
  · iexists x; iframe; ipureintro
    rw [Hl, List.getElem?_append_right (Nat.le_refl _)]; simp

/-- Decided slots accumulated in three parallel lists (the body of `decidedSlotsP`). -/
def decAcc (γ : QNames) (is : List w64) (ps : List w32) (dsls : List GoSlice) : IProp GF :=
  iprop(∃ ds : List (List GoString),
    ⌜is.length = ds.length ∧ ps.length = ds.length ∧ dsls.length = ds.length⌝ ∗
    [∗list] k ↦ d ∈ ds, ∃ (sl : GoSlice) (i : w64), ⌜dsls[k]? = some sl ∧ is[k]? = some i ∧
      ∀ x ∈ d, strOk x⌝ ∗ sl ↦*□ d ∗ decided γ (sint.Z i) d)

instance decAcc_persistent (γ : QNames) (is : List w64) (ps : List w32) (dsls : List GoSlice) :
    Persistent (decAcc (GF := GF) γ is ps dsls) := by unfold decAcc; infer_instance

theorem decAcc_nil (γ : QNames) : ⊢ decAcc (GF := GF) γ [] [] [] := by
  unfold decAcc; iexists []
  isplitr
  · ipureintro; simp
  · iapply BigSepL.bigSepL_nil.2; iempintro

theorem decAcc_snoc (γ : QNames) (is : List w64) (ps : List w32) (dsls : List GoSlice)
    (i : w64) (p : w32) (sl : GoSlice) (d : List GoString) (hd : ∀ x ∈ d, strOk x) :
    decAcc (GF := GF) γ is ps dsls ∗ sl ↦*□ d ∗ decided γ (sint.Z i) d ⊢
      decAcc γ (is ++ [i]) (ps ++ [p]) (dsls ++ [sl]) := by
  unfold decAcc
  iintro ⟨⟨%ds, %Hl, Hs⟩, #Hsl, #Hd⟩
  iexists ds ++ [d]
  isplitr
  · ipureintro; simp [Hl.1, Hl.2.1, Hl.2.2]
  iapply (BigSepL.bigSepL_snoc (Φ := fun k d => iprop(∃ (sl' : GoSlice) (i' : w64),
    ⌜(dsls ++ [sl])[k]? = some sl' ∧ (is ++ [i])[k]? = some i' ∧ ∀ x ∈ d, strOk x⌝ ∗
    sl' ↦*□ d ∗ decided γ (sint.Z i') d))).2
  isplitl [Hs]
  · iapply BigSepL.bigSepL_mono (Φ := fun k d => iprop(∃ (sl' : GoSlice) (i' : w64),
      ⌜dsls[k]? = some sl' ∧ is[k]? = some i' ∧ ∀ x ∈ d, strOk x⌝ ∗
      sl' ↦*□ d ∗ decided γ (sint.Z i') d))
      (fun {k d'} hk => by
        have hk' : k < ds.length := (List.getElem?_eq_some_iff.1 hk).1
        iintro ⟨%sl', %i', %Hf, H1, H2⟩
        iexists sl', i'; iframe; ipureintro
        refine ⟨?_, ?_, Hf.2.2⟩
        · rw [List.getElem?_append_left (by omega)]; exact Hf.1
        · rw [List.getElem?_append_left (by omega)]; exact Hf.2.1) $$ Hs
  · iexists sl, i; iframe #; ipureintro
    refine ⟨?_, ?_, hd⟩
    · rw [← Hl.2.2, List.getElem?_append_right (Nat.le_refl _)]; simp
    · rw [← Hl.1, List.getElem?_append_right (Nat.le_refl _)]; simp

theorem decidedSlotsP_of (γ : QNames) (isl psl dsl : GoSlice) (is : List w64) (ps : List w32)
    (dsls : List GoSlice) :
    isl ↦*□ is ∗ psl ↦*□ ps ∗ dsl ↦*□ dsls ∗ decAcc (GF := GF) γ is ps dsls ⊢
      decidedSlotsP γ isl psl dsl := by
  unfold decidedSlotsP decAcc
  iintro ⟨#H1, #H2, #H3, ⟨%ds, %Hl, #Hs⟩⟩
  iexists is, ps, dsls, ds
  iframe #
  ipureintro; exact Hl

instance repList_persistent {A : Type} (rep : Loc → DFrac → A → IProp GF) (ps : List Loc)
    (xs : List A) [h : ∀ p x, Persistent (rep p .discard x)] :
    Persistent (repList rep ps .discard xs) := by
  unfold repList; infer_instance

instance repPMSingle_persistent (l : Loc) (m : GoString) :
    Persistent (repPMSingle (GF := GF) l .discard m) := by unfold repPMSingle; infer_instance
instance repPMBatch_persistent (l : Loc) (b : Batch) :
    Persistent (repPMBatch (GF := GF) l .discard b) := by unfold repPMBatch; infer_instance
instance repPMSlot_persistent (l : Loc) (d : DSlot) :
    Persistent (repPMSlot (GF := GF) l .discard d) := by unfold repPMSlot; infer_instance
instance repProp_persistent (l : Loc) (p : Prop') :
    Persistent (repProp (GF := GF) l .discard p) := by unfold repProp; infer_instance
instance repPM_persistent (l : Loc) (m : PM) :
    Persistent (repPM (GF := GF) l .discard m) := by
  unfold repPM; cases m.p <;> infer_instance
instance repDReq_persistent (l : Loc) (ids : List GoString) :
    Persistent (repDReq (GF := GF) l .discard ids) := by unfold repDReq; infer_instance
instance repDecSlot_persistent (l : Loc) (d : DSlot) :
    Persistent (repDecSlot (GF := GF) l .discard d) := by unfold repDecSlot; infer_instance
instance repDecs_persistent (l : Loc) (ds : List DSlot) :
    Persistent (repDecs (GF := GF) l .discard ds) := by unfold repDecs; infer_instance
instance repCSingle_persistent (l : Loc) (m : GoString) :
    Persistent (repCSingle (GF := GF) l .discard m) := by unfold repCSingle; infer_instance
instance repCBVal_persistent (x : raxos.proto.client.ClientBatch) (b : Batch) :
    Persistent (repCBVal (GF := GF) x .discard b) := by unfold repCBVal; infer_instance
instance repDRSingle_persistent (l : Loc) (m : GoString) :
    Persistent (repDRSingle (GF := GF) l .discard m) := by unfold repDRSingle; infer_instance
instance repDRBatch_persistent (l : Loc) (b : Batch) :
    Persistent (repDRBatch (GF := GF) l .discard b) := by unfold repDRBatch; infer_instance
instance repRRProp_persistent (l : Loc) (p : RRProp) :
    Persistent (repRRProp (GF := GF) l .discard p) := by unfold repRRProp; infer_instance

instance repOpt_persistent {A : Type} (rep : Loc → DFrac → A → IProp GF) (l : Loc) (o : Option A)
    [h : ∀ l x, Persistent (rep l .discard x)] : Persistent (repOpt rep l .discard o) := by
  cases o <;> unfold repOpt <;> infer_instance
instance repRR_persistent (l : Loc) (r : RR) :
    Persistent (repRR (GF := GF) l .discard r) := by unfold repRR; infer_instance
instance repDResp_persistent (l : Loc) (bs : List Batch) :
    Persistent (repDResp (GF := GF) l .discard bs) := by unfold repDResp; infer_instance

instance repEmpty_persistent (l : Loc) :
    Persistent (repEmpty (GF := GF) l .discard) := by unfold repEmpty; infer_instance

end persist

end Perennial.raxos
