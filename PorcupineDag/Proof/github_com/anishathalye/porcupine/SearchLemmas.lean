/- Lean-first (no Rocq counterpart).

# Lemmas of the DAG search's proofs (2026-11-02)

For `chains.lift`, `chains.unlift` and `checkSingle`: a client's struct depends on the chains'
state only at that client (`ChAgree`, `clientOwn_agree`), and the access to one client of the
chains (`chainsOwn_acc`: the client's element pointer, its `clientOwn`, and the chains back at a
state that agrees elsewhere, with the same frontier).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Search

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

/-- Two chains' states agree at client `c`. -/
def ChAgree (st st' : ChSt) (c : Nat) : Prop :=
  st'.head c = st.head c ∧ st'.nDeps.getD c 0 = st.nDeps.getD c 0 ∧
  st'.vis.getD c [] = st.vis.getD c [] ∧ st'.fu.getD c [] = st.fu.getD c []

section bi
variable {PROP : Type _} [BI PROP] [BIAffine PROP] {A : Type _}

/-- A big separating conjunction with one element replaced and the predicate changed. -/
theorem bigSepL_set_change {Φ Ψ : Nat → A → PROP} {l : List A} {j : Nat} {x : A} (y : A)
    (hx : l[j]? = some x) :
    ([∗list] k ↦ z ∈ l, if k = j then emp else Φ k z) ⊢
      (□ ∀ k z, ⌜k ≠ j⌝ → Φ k z -∗ Ψ k z) -∗ Ψ j y -∗ [∗list] k ↦ z ∈ l.set j y, Ψ k z := by
  iintro Hl #Himp Hy
  have hy : (l.set j y)[j]? = some y := by
    rw [List.getElem?_set_self]; exact (List.getElem?_eq_some_iff.mp hx).1
  icases (BigSepL.bigSepL_insert_acc hx).trans (sep_mono_right (forall_elim y)) $$ Hl with ⟨-, Hl⟩
  ihave Hl := Hl $$ []
  · simp only [↓reduceIte]; iempintro
  icases BigSepL.bigSepL_lookup_acc_impl hy $$ Hl with ⟨-, Hl⟩
  iapply Hl $$ [] Hy
  imodintro
  iintro %k %z %_ %Hk Hz
  simp only [Hk, ↓reduceIte]
  iapply Himp $$ %k %z %Hk Hz

end bi

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem clientOwn_agree (h : List (Op OpV)) (cs : List (List Nat)) {st st' : ChSt} {c : Nat}
    (cv : client) (ha : ChAgree st st' c) :
    clientOwn h cs st c cv ⊢ clientOwn (GF := GF) h cs st' c cv := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  unfold clientOwn ChSt.fuAt
  rw [h1, h2, h3, h4]

/-- One client of a chains value: its element pointer and struct; the value comes back at any
state that agrees at the other clients, with the same frontier. -/
theorem chainsRepr_acc (chV : chains) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt)
    (j : Nat) (hj : j < cs.length) :
    chainsRepr chV h cs st ⊢ ⌜sint.Z chV.clients'.len = cs.length⌝ ∗ ∃ cv : client,
      sliceIndexRef client (j : Int) chV.clients' ↦ cv ∗ clientOwn (GF := GF) h cs st j cv ∗
      ∀ (st' : ChSt) (cv' : client), ⌜(∀ c, c ≠ j → ChAgree st st' c) ∧ st'.frontier = st.frontier⌝ -∗
        sliceIndexRef client (j : Int) chV.clients' ↦ cv' -∗ clientOwn h cs st' j cv' -∗
        chainsRepr chV h cs st' := by
  iintro Hr
  unfold chainsRepr
  icases Hr with ⟨%cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  ihave %Hlen := ownSlice_len $$ Hcl
  obtain ⟨cv, hcv⟩ : ∃ cv, cvs[j]? = some cv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases ownSlice_elem_acc (j : Int) cv _ _ cvs (by omega) (by simpa using hcv) $$ Hcl with ⟨He, Hcl⟩
  icases BigSepL.bigSepL_lookup_acc_impl hcv $$ Hcls with ⟨Hc, Hcls⟩
  isplitr
  · ipureintro; obtain ⟨h1, h2⟩ := Hlen; rw [← Hcvs.1]; word
  iexists cv
  iframe He Hc
  iintro %st' %cv' %Hag He Hc
  obtain ⟨Hag, Hfr'⟩ := Hag
  iexists cvs.set j cv'
  ihave Hcl := Hcl $$ %cv' He
  simp only [Int.toNat_natCast]
  iframe Hcl
  rw [Hfr']
  iframe Hfr Hcap
  isplitr
  · ipureintro; simpa using Hcvs
  iapply bigSepL_set_change cv' hcv $$ [Hcls] [] Hc
  · iapply Hcls $$ [] []
    · imodintro
      iintro %k %y %_ %Hk Hy
      simp only [Hk, ↓reduceIte]
      iexact Hy
    · simp only [↓reduceIte]; iempintro
  imodintro
  iintro %k %y %Hk Hy
  iapply clientOwn_agree h cs y (Hag k Hk) $$ Hy

/-- The chains at `ch`, with their clients slice `cl` (fixed by every helper: only the frontier
field is ever stored to). -/
def chainsOwnCl (ch : Loc) (cl : GoSlice) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) :
    IProp GF :=
  iprop(∃ chV : chains, ch ↦ chV ∗ ⌜chV.clients' = cl⌝ ∗ chainsRepr chV h cs st)

theorem chainsOwnCl_weaken (ch : Loc) (cl : GoSlice) (h : List (Op OpV)) (cs : List (List Nat))
    (st : ChSt) : chainsOwnCl ch cl h cs st ⊢ chainsOwn (GF := GF) ch h cs st := by
  unfold chainsOwnCl chainsOwn
  iintro ⟨%chV, Hch, -, Hr⟩
  iexists chV
  iframe

theorem chainsOwnCl_fold (ch : Loc) (chV : chains) (cl : GoSlice) (h : List (Op OpV))
    (cs : List (List Nat)) (st : ChSt) (hcl : chV.clients' = cl) :
    ch ↦ chV ∗ chainsRepr chV h cs st ⊢ chainsOwnCl (GF := GF) ch cl h cs st := by
  unfold chainsOwnCl
  iintro ⟨Hch, Hr⟩
  iexists chV
  iframe
  ipureintro; exact hcl

theorem chainsOwn_cl (ch : Loc) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) :
    chainsOwn ch h cs st ⊢ ∃ cl, chainsOwnCl (GF := GF) ch cl h cs st := by
  unfold chainsOwnCl chainsOwn
  iintro ⟨%chV, Hch, Hr⟩
  iexists chV.clients', chV
  iframe
  ipureintro; rfl

/-- One client of the chains (`chainsRepr_acc`), at a known clients slice. -/
theorem chainsOwnCl_acc (ch : Loc) (cl : GoSlice) (h : List (Op OpV)) (cs : List (List Nat))
    (st : ChSt) (j : Nat) (hj : j < cs.length) :
    chainsOwnCl ch cl h cs st ⊢ ∃ (chV : chains) (cv : client), ch ↦ chV ∗
      ⌜chV.clients' = cl ∧ sint.Z cl.len = cs.length⌝ ∗
      sliceIndexRef client (j : Int) cl ↦ cv ∗ clientOwn (GF := GF) h cs st j cv ∗
      ∀ (st' : ChSt) (cv' : client), ⌜(∀ c, c ≠ j → ChAgree st st' c) ∧ st'.frontier = st.frontier⌝ -∗
        ch ↦ chV -∗ sliceIndexRef client (j : Int) cl ↦ cv' -∗ clientOwn h cs st' j cv' -∗
        chainsOwnCl ch cl h cs st' := by
  iintro Hch
  unfold chainsOwnCl
  icases Hch with ⟨%chV, Hch, %Hcl, Hr⟩
  subst Hcl
  icases chainsRepr_acc chV h cs st j hj $$ Hr with ⟨%Hlen, %cv, He, Hc, Hback⟩
  iexists chV, cv
  iframe Hch He Hc
  isplitr
  · ipureintro; exact ⟨rfl, Hlen⟩
  iintro %st' %cv' %Hag Hch He Hc
  iexists chV
  iframe Hch
  isplitr
  · ipureintro; rfl
  iapply Hback $$ %st' %cv' %Hag He Hc

/-- One client of the chains. -/
theorem chainsOwn_acc (ch : Loc) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (j : Nat)
    (hj : j < cs.length) :
    chainsOwn ch h cs st ⊢ ∃ (chV : chains) (cv : client),
      ch ↦ chV ∗ ⌜sint.Z chV.clients'.len = cs.length⌝ ∗
      sliceIndexRef client (j : Int) chV.clients' ↦ cv ∗ clientOwn (GF := GF) h cs st j cv ∗
      ∀ (st' : ChSt) (cv' : client), ⌜(∀ c, c ≠ j → ChAgree st st' c) ∧ st'.frontier = st.frontier⌝ -∗
        ch ↦ chV -∗ sliceIndexRef client (j : Int) chV.clients' ↦ cv' -∗ clientOwn h cs st' j cv' -∗
        chainsOwn ch h cs st' := by
  iintro Hch
  icases chainsOwn_cl ch h cs st $$ Hch with ⟨%cl, Hch⟩
  icases chainsOwnCl_acc ch cl h cs st j hj $$ Hch with ⟨%chV, %cv, Hch, %Hl, He, Hc, Hback⟩
  obtain ⟨rfl, Hl⟩ := Hl
  iexists chV, cv
  iframe Hch He Hc
  isplitr
  · ipureintro; exact Hl
  iintro %st' %cv' %Hag Hch He Hc
  iapply chainsOwnCl_weaken
  iapply Hback $$ %st' %cv' %Hag Hch He Hc

theorem clientOwn_facts (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (c : Nat)
    (cv : client) :
    clientOwn h cs st c cv ⊢ ⌜sint.Z cv.id' = c ∧ sint.Z cv.head' = st.head c ∧
      cv.nDeps' = st.nDeps.getD c 0⌝ ∗ clientOwn (GF := GF) h cs st c cv := by
  unfold clientOwn
  iintro ⟨%Hc, Hr⟩
  iframe Hr
  ipureintro; exact ⟨Hc, Hc⟩

/-- A client's struct, with its head or `nDeps` changed. -/
theorem clientOwn_upd (h : List (Op OpV)) (cs : List (List Nat)) {st st' : ChSt} {c : Nat}
    (cv cv' : client) (hcl : cv'.cltOps' = cv.cltOps') (hid : cv'.id' = cv.id')
    (hhd : sint.Z cv'.head' = st'.head c) (hnd : cv'.nDeps' = st'.nDeps.getD c 0)
    (hv : st'.vis.getD c [] = st.vis.getD c []) (hf : st'.fu.getD c [] = st.fu.getD c []) :
    clientOwn h cs st c cv ⊢ clientOwn (GF := GF) h cs st' c cv' := by
  unfold clientOwn ChSt.fuAt
  iintro ⟨%Hc, %cos, Hcos, %Hok, Hfu⟩
  isplitr
  · ipureintro; exact ⟨by rw [hid]; exact Hc.1, hhd, hnd⟩
  iexists cos
  rw [hcl, hv, hf]
  iframe
  ipureintro; exact Hok

theorem stackRep_length (S : ModelSpec GF σ) (np : NaInvPoolName) (cs : List (List Nat))
    (ses : List stackEntry) (fs : List (Frame σ)) [NaInvG GF] :
    stackRep S np cs ses fs ⊢ ⌜ses.length = fs.length⌝ := by
  unfold stackRep
  iintro H
  ihave %h := BigSepL2.bigSepL2_length $$ H
  ipureintro; simpa using h

/-- The newest frame is the stack's last entry. -/
theorem stackRep_pop (S : ModelSpec GF σ) (np : NaInvPoolName) (cs : List (List Nat))
    (ses : List stackEntry) (f : Frame σ) (fs : List (Frame σ)) [NaInvG GF] :
    stackRep S np cs ses (f :: fs) ⊢ ∃ (ses' : List stackEntry) (se : stackEntry),
      ⌜ses = ses' ++ [se] ∧ sint.Z se.opId' = f.id ∧ sint.Z se.clientId' = clientOf cs f.id ∧
        sint.Z se.frontierIdx' = f.pos⌝ ∗ shared S np fs.length se.state' f.pre ∗
      stackRep S np cs ses' fs := by
  unfold stackRep
  simp only [List.reverse_cons]
  iintro H
  icases BigSepL2.bigSepL2_app_inv_right $$ H with ⟨%l1, %l2, %hses, H1, H2⟩
  ihave %hl2 := BigSepL2.bigSepL2_length $$ H2
  simp only [List.length_singleton] at hl2
  obtain ⟨se, rfl⟩ : ∃ se, l2 = [se] := by
    cases l2 with
    | nil => simp at hl2
    | cons a l => cases l with
      | nil => exact ⟨a, rfl⟩
      | cons b l => simp at hl2
  icases BigSepL2.bigSepL2_singleton.1 $$ H2 with ⟨%he, #Hs⟩
  iexists l1, se
  rw [show fs.length = 0 + fs.reverse.length by simp]
  iframe H1 Hs
  ipureintro; exact ⟨hses, he⟩

/-- A frame pushed: a new last entry. -/
theorem stackRep_push (S : ModelSpec GF σ) (np : NaInvPoolName) (cs : List (List Nat))
    (ses : List stackEntry) (se : stackEntry) (f : Frame σ) (fs : List (Frame σ)) [NaInvG GF]
    (hse : sint.Z se.opId' = f.id ∧ sint.Z se.clientId' = clientOf cs f.id ∧
      sint.Z se.frontierIdx' = f.pos) :
    stackRep S np cs ses fs ∗ shared S np fs.length se.state' f.pre ⊢
      stackRep S np cs (ses ++ [se]) (f :: fs) := by
  iintro ⟨H, #Hs⟩
  ihave %hl := stackRep_length S np cs ses fs $$ H
  unfold stackRep
  simp only [List.reverse_cons]
  iapply BigSepL2.bigSepL2_snoc.2
  iframe H
  rw [hl]
  iframe Hs
  ipureintro; exact hse

end heap

end github_com.anishathalye.porcupine

end Perennial
