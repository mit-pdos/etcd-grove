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

/-- One client of the chains: its element pointer and struct; the chains come back at any state
that agrees at the other clients, with the same frontier. -/
theorem chainsOwn_acc (ch : Loc) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (j : Nat)
    (hj : j < cs.length) :
    chainsOwn ch h cs st ⊢ ∃ (chV : chains) (cv : client),
      ch ↦ chV ∗ ⌜sint.Z chV.clients'.len = cs.length⌝ ∗
      sliceIndexRef client (j : Int) chV.clients' ↦ cv ∗ clientOwn (GF := GF) h cs st j cv ∗
      ∀ (st' : ChSt) (cv' : client), ⌜(∀ c, c ≠ j → ChAgree st st' c) ∧ st'.frontier = st.frontier⌝ -∗
        ch ↦ chV -∗ sliceIndexRef client (j : Int) chV.clients' ↦ cv' -∗ clientOwn h cs st' j cv' -∗
        chainsOwn ch h cs st' := by
  iintro Hch
  unfold chainsOwn chainsRepr
  icases Hch with ⟨%chV, Hch, %cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  ihave %Hlen := ownSlice_len $$ Hcl
  obtain ⟨cv, hcv⟩ : ∃ cv, cvs[j]? = some cv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases ownSlice_elem_acc (j : Int) cv _ _ cvs (by omega) (by simpa using hcv) $$ Hcl with ⟨He, Hcl⟩
  icases BigSepL.bigSepL_lookup_acc_impl hcv $$ Hcls with ⟨Hc, Hcls⟩
  iexists chV, cv
  iframe Hch He Hc
  isplitr
  · ipureintro; obtain ⟨h1, h2⟩ := Hlen; rw [← Hcvs.1]; word
  iintro %st' %cv' %Hag Hch He Hc
  obtain ⟨Hag, Hfr'⟩ := Hag
  iexists chV
  iframe Hch
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

end heap

end github_com.anishathalye.porcupine

end Perennial
