/-
`sort.Search`, with the indices it evaluates (U6, `notes/bbolt-proof-plan.md`): a stronger spec of
Perennial's translated `sort.Search`, proved here from its code. The invariant is indexed by the
list of indices `f` was called at, and a result below `n` is one of them (the loop's `j` is `n` or
an index it called `f` at). `Cursor.searchPage` needs it: its closure records an exact match in a
captured variable, which is right only if the returned index was evaluated. (A general fact about
Perennial's `sort.Search`: a candidate for Perennial's own spec, `notes/perennial-changes.md`.)
-/
module

public import Perennial.Spec.sort.Search

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Read

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- The predicate function implements `f` on `[0, n)`, its invariant indexed by the indices it was
called at (newest first). -/
def predImplementsL (f_code : GoFunc) (f : Int → Bool) (n : Int) (I : List Int → IProp GF) :
    IProp GF :=
  iprop(∀ (L : List Int) (i : w64),
    {{ I L ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < n⌝ }}
      (App (Val #f_code) (Val #i))
    {{ (r : Bool), RET #r; I (sint.Z i :: L) ∗ ⌜r = f (sint.Z i)⌝ }})

instance predImplementsL_persistent (f_code : GoFunc) (f : Int → Bool) (n : Int)
    (I : List Int → IProp GF) : Persistent (predImplementsL f_code f n I) := by
  unfold predImplementsL; infer_instance

abbrev sort.SearchEv.spec : Prop :=
  ∀ (n : w64) (f_code : GoFunc) (f : Int → Bool) (I : List Int → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ ⌜0 ≤ sint.Z n⌝ ∗
        predImplementsL f_code f (sint.Z n) I ∗ I [] ∗ ⌜sort.IsMonoPred f (sint.Z n)⌝ }}
      (App (App (Val (@! sort.Search)) (Val #n)) (Val #f_code))
    {{ (i : w64), RET #i; ∃ L, I L ∗
        ⌜0 ≤ sint.Z i⌝ ∗
        ⌜sint.Z i < sint.Z n → f (sint.Z i) = true⌝ ∗
        ⌜(∀ i, 0 ≤ i ∧ i < sint.Z n → f i = false) → sint.Z i = sint.Z n⌝ ∗
        ⌜∀ k, 0 ≤ k ∧ k < sint.Z i → f k = false⌝ ∗
        ⌜sint.Z i < sint.Z n → sint.Z i ∈ L⌝ }}

theorem sort.SearchEv.wp_proof : sort.SearchEv.spec (GF := GF) (hG := hG) :=
    fun n f_code f I => by
  wp_start as ⟨%Hpos, #Hf, I0, %Hmono0⟩
  wp_auto
  have Hvalid := sort.isValidPred_adapted f (sint.Z n) Hpos Hmono0
  obtain ⟨Hmono, Hneg, Hn⟩ := Hvalid
  unfold predImplementsL
  ihave HI : (∃ (i j : w64) (L : List Int),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "I" ∷ I L ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z n⌝ ∗
      "%Hi_prop" ∷ ⌜sort.adaptPred f (sint.Z n) (sint.Z i - 1) = false⌝ ∗
      "%Hj_prop" ∷ ⌜sort.adaptPred f (sint.Z n) (sint.Z j) = true⌝ ∗
      "%Hj_ev" ∷ ⌜sint.Z j < sint.Z n → sint.Z j ∈ L⌝ : IProp GF) $$ [i j I0]
  · iexists _, _, []
    iframe
    ipureintro
    refine ⟨by word, ?_, Hn, fun h => by omega⟩
    rw [show sint.Z (W64 0) - 1 = -1 by decide, Hneg]
  wp_for HI
  wp_if_destruct
  · have Hj : sint.Z i ≤ sint.Z ((i + j) >>> W64 1) ∧ sint.Z ((i + j) >>> W64 1) < sint.Z j := by
      rw [sort.shiftr_1_eq_div]; word'
    wp_apply Hf $$ [I] with %r ⟨I, %Hf_result⟩
    · iframe I; ipureintro; omega
    generalize (i + j) >>> W64 1 = h at Hj Hf_result ⊢
    have Hfh : sort.adaptPred f (sint.Z n) (sint.Z h) = f (sint.Z h) :=
      sort.adaptPred_bounded _ _ _ (by omega)
    cases r
    · simp only [Bool.not_false]
      wp_auto
      wp_for_post
      iframe
      iexists (h + W64 1), j, (sint.Z h :: L)
      iframe
      ipureintro
      refine ⟨by word, ?_, Hj_prop, fun hj => List.mem_cons_of_mem _ (Hj_ev hj)⟩
      have : sint.Z (h + W64 1) - 1 = sint.Z h := by word
      rw [this, Hfh, ← Hf_result]
    · simp only [Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists i, h, (sint.Z h :: L)
      iframe
      ipureintro
      exact ⟨by word, Hi_prop, by rw [Hfh]; exact Hf_result.symm, fun _ => List.mem_cons_self ..⟩
  · have Hij : sint.Z i = sint.Z j := by omega
    iapply HΦ
    iexists L
    iframe I
    ipureintro
    refine ⟨by omega, ?_, ?_, ?_, fun h => by rw [Hij] at h ⊢; exact Hj_ev h⟩
    · intro Hilt
      rw [← Hij, sort.adaptPred_bounded _ _ _ (by omega)] at Hj_prop
      exact Hj_prop
    · intro Hno_true
      by_cases hlt : sint.Z i < sint.Z n
      · rw [← Hij, sort.adaptPred_bounded _ _ _ (by omega)] at Hj_prop
        have := Hno_true (sint.Z i) (by omega)
        simp_all
      · omega
    · intro k Hk
      by_cases hk : k = sint.Z i - 1
      · subst hk; rwa [sort.adaptPred_bounded _ _ _ (by omega)] at Hi_prop
      · cases hfk : f k
        · rfl
        · have := Hmono k (sint.Z i - 1) (by omega)
            (by rw [sort.adaptPred_bounded _ _ _ (by omega)]; exact hfk)
          simp_all

end spec

end Read

end bbolt
end EtcdGrove
end Perennial
