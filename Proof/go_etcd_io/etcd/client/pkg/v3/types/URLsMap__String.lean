/-
Proof of `types.URLsMap.String.spec` (claim #34, stage 2, 2026-11-25): the range over the map, the
range over each entry's URLs (`fmt.Sprintf("%s=%s", name, url.String())` appended), `sort.Strings`,
`strings.Join`.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLsMap__String
public import Proof.fmt.OutLemmas
public import Perennial.Spec.sort.Strings
public import Perennial.Spec.strings.Join

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
before the `i`-th iteration, and the body ends normally. (A copy of
`Proof/k8s_io/api/DeepCopyBase.lean`'s `wp_slice_for_range`, which this package does not import.) -/
private theorem wp_slice_for_range_ro {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  unfold slice.forRange
  wp_auto
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
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv ⟨%hbv, HP, Hs⟩
    subst hbv
    iapply wp_for_post_do
    wp_auto
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
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

theorem types.URLsMap.String.wp_proof
    (hURL : http.URLStringAny_spec (GF := GF))
    (hSprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (hSort : sort.Strings.spec (GF := GF) (hG := hG))
    (hJoin : strings.Join.spec (GF := GF) (hG := hG)) :
    types.URLsMap.String.spec (GF := GF) (hG := hG) := by
  intro mp m urls Hsum
  wp_start as ⟨#Hm, #Hurls⟩
  have hSp := fmt.Sprintf.argsWf hSprintf
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoSlice) (fun keys i => iprop(
      ∃ (ps : GoSlice) (xs : List GoString) (nm : GoString) (us : GoSlice),
      "%Hi" ∷ ⌜0 ≤ i ∧ xs.length = ((keys.take i.toNat).map (fun k => (urls k).length)).sum⌝ ∗
      "pairs" ∷ pairs_ptr ↦ ps ∗ "Hps" ∷ ps ↦* xs ∗ "Hcap" ∷ ownSliceCap GoString ps (DFrac.own 1) ∗
      "name" ∷ name_ptr ↦ nm ∗ "urls" ∷ urls_ptr ↦ us)) _ _ _ mp m DFrac.discard) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [pairs name urls]
  · iexists slice.nil, [], _, _
    iframe pairs name urls
    isplitr
    · ipureintro; simp
    isplitl []
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    obtain ⟨Hi0, Hxs⟩ := Hi
    ihave #Hvu : (vv ↦*□ urls key : IProp GF) $$ [Hurls]
    · iapply (BigSepM.bigSepM_lookup (Φ := fun k sl => (sl ↦*□ urls k : IProp GF)) Hvv) $$ Hurls
    (try wp_auto)
    wp_apply (wp_slice_for_range_ro (V := _root_.Perennial.net.url.URL) _ vv (urls key) DFrac.discard _
      (fun j => iprop(∃ (ps : GoSlice) (xs' : List GoString),
        ⌜xs'.length = xs.length + j⌝ ∗ pairs_ptr ↦ ps ∗ ps ↦* xs' ∗
        ownSliceCap GoString ps (DFrac.own 1) ∗ name_ptr ↦ key))) $$ Hvu [pairs Hps Hcap name]
    · iexists ps, xs
      iframe
      ipureintro; rfl
    · imodintro
      iintro %j %x %hx ⟨%ps2, %xs2, %Hl2, pairs, Hps, Hcap, name⟩ -
      (try wp_auto)
      wp_apply (hURL url_ptr (DFrac.own 1) x) $$ [url] as %s ⟨url, -⟩
      · iexact url
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoInterface)
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_apply (hSp _ _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string _ _
          (_root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil)))
        $$ [$Hasl] as %str -
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoString)
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append (V := GoString) _ _ _ _ _ $$ [$Hps $Hcap $Hsl1] as %ps3 ⟨Hps, Hcap, -⟩
      (try wp_auto)
      isplitr
      · ipureintro; rfl
      iexists ps3, xs2 ++ [str]
      iframe
      ipureintro; simp [Hl2]; omega
    iintro ⟨%ps2, %xs2, %Hl2, pairs, Hps, Hcap, name⟩ -
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists ps2, xs2, key, vv
    iframe
    ipureintro
    have hi1 : (i + 1).toNat = i.toNat + 1 := by omega
    refine ⟨by omega, ?_⟩
    rw [hi1, List.take_succ, Hkey, Hl2, Hxs]
    simp
  iintro HP -
  iNamed HP
  obtain ⟨Hi0, Hxs⟩ := Hi
  have htake : keys.take (GMap.size m : Int).toNat = keys := by
    rw [List.take_of_length_le]; omega
  rw [htake] at Hxs
  have hperm : keys.Perm m.domList :=
    (List.perm_ext_iff_of_nodup Hknodup (GMap.nodup_dom_list m)).2
      (fun k => (Hkset k).trans (GMap.mem_dom_list m k).symm)
  have hlen : xs.length ≤ 2 ^ 62 := by
    rw [Hxs, (hperm.map _).sum_eq]; exact Hsum
  (try wp_auto)
  ihave #Hsortp : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  wp_apply hSort ps xs $$ [Hps] as %xs' ⟨Hps, -, -⟩
  · iframe #; iframe; ipureintro; exact hlen
  (try wp_auto)
  ihave #Hstrp : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_apply hJoin ps xs' (DFrac.own 1) go!"," $$ [Hps] as Hps
  · iframe #; iframe
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
