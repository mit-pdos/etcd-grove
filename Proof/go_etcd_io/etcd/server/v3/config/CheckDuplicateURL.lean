/-
Proof of `config.CheckDuplicateURL.spec` (claim #34, stage 2, 2026-11-25): the range over the map and
over each entry's URLs, a local `map[string]bool` of the URL strings seen (`url.String()`, over
`http.URLStringAny_spec`); `return true` from inside the inner range on a repeat (the continuation
carried in the loops' invariants), `false` after.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.CheckDuplicateURL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

attribute [-instance] pure_wp_slice_for_range

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A range loop over a slice the loop only reads** (`for i, x := range s { body }`): `P i` holds
before the `i`-th iteration, and the body ends normally or returns (`Φ` of its return). (A copy of
`Proof/k8s_io/api/DeepCopyBase.lean`'s `wp_slice_for_range`, which this package does not import.) -/
private theorem wp_slice_for_range_ret {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, (⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs) ∨
            (∃ v, ⌜bv = returnVal v⌝ ∗ Φ bv) }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  unfold slice.forRange
  try wp_auto
  ihave Hinv : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 j ∗ "HP" ∷ P j ∗ "Hs" ∷ sl ↦*{dq} vs ∗
      "HΦ" ∷ (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) ∗ "%Hj" ∷ ⌜j ≤ vs.length⌝ :
      IProp GF) $$ [i HP Hs HΦ]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for Hinv
  by_cases hj : j < vs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    try wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv (⟨%hbv, HP, Hs⟩ | ⟨%v, %hbv, HΦr⟩)
    rotate_left
    · subst hbv
      iapply wp_for_post_return
      (try wp_auto)
      iexact HΦr
    subst hbv
    iapply wp_for_post_do
    try wp_auto
    iframe
    iexists (j + 1)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    have hj1 : j + 1 ≤ vs.length := hj
    iframe
    ipureintro; exact hj1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = vs.length := by omega
    subst hjl
    iapply HΦ $$ HP Hs

end loop

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

theorem config.CheckDuplicateURL.wp_proof
    (hURL : http.URLStringAny_spec (GF := GF)) :
    config.CheckDuplicateURL.spec (GF := GF) (hG := hG) := by
  intro mp m urls
  wp_start as ⟨#Hm, #Hurls⟩
  ihave HΦ' : (∀ b : Bool, Φ #b) $$ [HΦ]
  · iintro %b; iapply HΦ; itrivial
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %ump Hump
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoSlice) (fun _ _ => iprop(
      ∃ (umm : GMap GoString Bool) (us : GoSlice) (r : Bool),
      "Hump" ∷ ump ↦$ umm ∗ "um" ∷ um_ptr ↦ ump ∗ "urls" ∷ urls_ptr ↦ us ∗
      "res0" ∷ «$res0_ptr» ↦ r ∗ "HΦ'" ∷ (∀ b : Bool, Φ #b))) _ _ _ mp m DFrac.discard) $$ Hm
  iintro %keys -
  isplitl [Hump um urls «$res0» HΦ']
  · iexists ∅, _, _
    iframe
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    ihave #Hvu : (vv ↦*□ urls key : IProp GF) $$ [Hurls]
    · iapply (BigSepM.bigSepM_lookup (Φ := fun k sl => (sl ↦*□ urls k : IProp GF)) Hvv) $$ Hurls
    (try wp_auto)
    wp_apply (wp_slice_for_range_ret (V := _root_.Perennial.net.url.URL) _ vv (urls key) DFrac.discard _
      (fun _ => iprop(∃ (umm : GMap GoString Bool) (r : Bool),
        "Hump" ∷ ump ↦$ umm ∗ "um" ∷ um_ptr ↦ ump ∗ "res0" ∷ «$res0_ptr» ↦ r ∗
        "HΦ'" ∷ (∀ b : Bool, Φ #b)))) $$ Hvu [Hump um res0 HΦ']
    · iexists umm, r
      iframe
    · imodintro
      iintro %j %x %hx HQ -
      iNamed HQ
      (try wp_auto)
      wp_apply (hURL url_ptr (DFrac.own 1) x) $$ [url] as %s ⟨url, -⟩
      · iexact url
      (try wp_auto)
      wp_apply (wp_map_lookup1 (K := GoString) (V := Bool) _ _ ump umm s (DFrac.own 1)) $$ [Hump]
        as Hump
      · iframe
      wp_if_destruct
      · -- a duplicate: `return true`
        (try wp_auto)
        iright
        iexists _
        isplitr
        · ipureintro; rfl
        (try wp_auto)
        unfold forMapPostcondition
        iright; iright; iright; ileft
        iexists _
        isplitr
        · ipureintro; rfl
        iintro -
        (try wp_auto)
        iapply HΦ'
      · (try wp_auto)
        wp_apply (wp_mapInsert (K := GoString) (V := Bool) _ ump umm s true) $$ [Hump] as Hump
        · iframe
        (try wp_auto)
        ileft
        isplitr
        · ipureintro; rfl
        iframe
        iexists _, _
        iframe
    iintro HQ -
    iNamed HQ
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _, vv, _
    iframe
  iintro HP -
  iNamed HP
  (try wp_auto)
  iapply HΦ'

end proof

end EtcdGrove
end Perennial
