/-
**`sort.Search` for any predicate** (the auth plan's S4d, 2026-10-24). Lean-first (no Rocq
counterpart). Perennial's `sort.Search.spec` needs the predicate to go from false to true
(`IsMonoPred`): the least index at which it holds. `RoleGrantPermission` searches a role's
permissions for the first whose key is not below the new one's, and nothing records that a role's
permissions are sorted by key (the backend's records are what the store reads: `Buckets.lean`);
its step (`roleGrantPermissionR`) holds at any index the search returns, so all it needs is an
index in `[0, n]`. This is that weaker fact, of Perennial's translation of `sort.Search`, proved
here as a workaround: the general spec (no monotonicity, the index in range and `f` false below it
up to the last probe, or just in range) belongs to Perennial (`notes/perennial-changes.md`,
"Specs: `sort.Search` without monotonicity").
-/
module

public import Perennial.Spec.sort.Search
public import Perennial.Proof.sort.SearchBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- **`sort.Search(n, f)` for any `f`**: an index in `[0, n]`, the predicate's resource kept. -/
theorem auth.wp_Search_any (n : w64) (f_code : GoFunc) (f : Int → Bool) (I : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        ⌜0 ≤ sint.Z n⌝ ∗
        _root_.Perennial.sort.predImplements f_code f (sint.Z n) I ∗
        I }}
      (App (App (Val (@! _root_.Perennial.sort.Search)) (Val #n)) (Val #f_code))
    {{ (i : w64), RET #i; I ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z n⌝ }} := by
  wp_start as ⟨%Hpos, #Hf, I⟩
  wp_auto
  unfold _root_.Perennial.sort.predImplements
  ihave HI : (∃ (i j : w64),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "I" ∷ I ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z n⌝ : IProp GF)
      $$ [i j I]
  · iexists _, _
    iframe
    ipureintro
    word
  wp_for HI
  wp_if_destruct
  · have Hj : sint.Z i ≤ sint.Z ((i + j) >>> W64 1) ∧ sint.Z ((i + j) >>> W64 1) < sint.Z j := by
      rw [_root_.Perennial.sort.shiftr_1_eq_div]; word'
    wp_apply Hf $$ [I] with %r ⟨I, -⟩
    · iframe I; ipureintro; omega
    generalize (i + j) >>> W64 1 = h at Hj ⊢
    cases r
    · simp only [Bool.not_false]
      wp_auto
      wp_for_post
      iframe
      iexists (h + W64 1), j
      iframe
      ipureintro
      word
    · simp only [Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists i, h
      iframe
      ipureintro
      word
  · iapply HΦ
    iframe I
    ipureintro
    omega

end proof

end EtcdGrove
end Perennial
