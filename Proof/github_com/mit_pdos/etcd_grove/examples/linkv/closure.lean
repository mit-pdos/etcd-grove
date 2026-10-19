/-
Lean-first (no Rocq counterpart).

The proof of `closure`: the worklist loop's invariant is `CloInv` (`ModelLemmas.lean`): every
configuration of `out` and `work` is reached from `s`'s and bounded, `s`'s are in `out` or
`work`, and the successors of `out`'s are in `out` or `work`. A configuration popped from `work`
is dropped if `addConfig` finds it in `out` (`cloInv_skip`), else added and its successors
pushed by the inner loop (`cloInv_add`); at the end `work` is empty (`cloInv_done`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.closure
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.addConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.set
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.removeAt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

theorem closure.wp_proof (wp_addConfig : addConfig.spec (GF := GF) (hG := hG))
    (wp_set : set.spec (GF := GF) (hG := hG)) (wp_removeAt : removeAt.spec (GF := GF) (hG := hG)) :
    closure.spec (GF := GF) (hG := hG) := by
  intro s cs gs dq
  wp_start as ⟨Hs, #Hcs, %Hb⟩
  ihave %Hl := ownSlice_len $$ Hs
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hcs
  wp_auto
  wp_apply wp_slice_literal (V := kvConfig) (l := [])
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Ho, Hocap⟩
  wp_auto
  wp_apply wp_slice_literal (V := kvConfig) (l := [])
  isplitr
  · ipureintro; rfl
  iintro %wsl ⟨Hw0, Hw0cap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hw0 $Hw0cap $Hs] as %w ⟨Hw, Hwcap, Hs⟩
  rw [List.nil_append]
  ihave HI : (∃ (so sw : GoSlice) (ocs wcs : List kvConfig) (ogs wgs : List GCfg),
      "out" ∷ out_ptr ↦ so ∗ "Ho" ∷ so ↦* ocs ∗ "Hocap" ∷ ownSliceCap kvConfig so (DFrac.own 1) ∗
      "work" ∷ work_ptr ↦ sw ∗ "Hw" ∷ sw ↦* wcs ∗
      "Hwcap" ∷ ownSliceCap kvConfig sw (DFrac.own 1) ∗
      "#Hocs" ∷ ([∗list] c;g ∈ ocs;ogs, cfgOwn c g) ∗
      "#Hwcs" ∷ ([∗list] c;g ∈ wcs;wgs, cfgOwn c g) ∗
      "%Hinv" ∷ ⌜CloInv gs ogs wgs⌝ : IProp GF) $$ [out Ho Hocap work Hw Hwcap]
  · iexists (slice.mk osl (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))), w,
      [], cs, [], gs
    iframe
    isplitl []
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
      iempintro
    isplitl []
    · iexact Hcs
    ipureintro; exact cloInv_init gs Hb
  wp_for HI
  ihave %Hwl := ownSlice_len $$ Hw
  ihave %Hwlen := BigSepL2.bigSepL2_length $$ Hwcs
  ihave %Hol := ownSlice_len $$ Ho
  ihave %Holen := BigSepL2.bigSepL2_length $$ Hocs
  wp_if_destruct
  · have Hpos : 0 < sint.Z sw.len := by
      have h0 : sint.Z (W64 0) = 0 := rfl
      rw [h0] at Hif; exact Hif
    obtain ⟨wc, d, rfl⟩ : ∃ wc d, wcs = wc ++ [d] := by
      rcases List.eq_nil_or_concat wcs with h0 | ⟨wc, d, h0⟩
      · exfalso; subst h0; simp only [List.length_nil] at Hwl; word
      · exact ⟨wc, d, by rw [h0, List.concat_eq_append]⟩
    obtain ⟨wg, h, rfl⟩ : ∃ wg h, wgs = wg ++ [h] := by
      rcases List.eq_nil_or_concat wgs with h0 | ⟨wg, h, h0⟩
      · exfalso; subst h0; simp at Hwlen
      · exact ⟨wg, h, by rw [h0, List.concat_eq_append]⟩
    simp only [List.length_append, List.length_singleton] at Hwl Hwlen
    icases (BigSepL2.bigSepL2_snoc (Φ := fun _ c g => cfgOwn (GF := GF) c g)).1 $$ Hwcs
      with ⟨#Hwc, #Hd⟩
    ihave %Hcw := ownSliceCap_wf $$ Hwcap
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index sw (sint.Z (sw.len - W64 1)) (wc ++ [d]) _ d (by word) $$ [Hw]
      as Hw
    · iframe; ipureintro
      rw [show (sint.Z (sw.len - W64 1)).toNat = wc.length by word]; simp
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
    icases ownSlice_slice_with_cap (W64 0) (sw.len - W64 1) sw (wc ++ [d])
      ⟨by word, by word, by word⟩ $$ [$Hw $Hwcap] with ⟨-, Hw, Hwcap⟩
    rw [show subslice (sint.nat (W64 0)) (sint.nat (sw.len - W64 1)) (wc ++ [d]) = wc by
      rw [show sint.nat (sw.len - W64 1) = wc.length by word, show sint.nat (W64 0) = 0 from rfl]
      simp [subslice]]
    wp_auto
    wp_apply wp_addConfig so ocs ogs d h $$ [$Ho $Hocap $Hocs $Hd] as %so' %ocs' ⟨Ho, Hocap, #Hocs'⟩
    ihave %Hol' := ownSlice_len $$ Ho
    ihave %Holen' := BigSepL2.bigSepL2_length $$ Hocs'
    rw [length_addConfigL] at Holen'
    by_cases hm : h ∈ ogs
    · -- already in `out`: dropped
      rw [if_pos hm] at Holen'
      have hlen : so'.len = so.len := by word
      rw [show addConfigL ogs h = ogs from if_pos hm, decide_eq_true hlen]
      wp_auto
      wp_for_post
      iframe
      iexists so', (slice.slice sw kvConfig (W64 0) (sw.len - W64 1)), ocs', wc, ogs, wg
      iframe
      isplitl []
      · iexact Hocs'
      isplitl []
      · iexact Hwc
      ipureintro; exact cloInv_skip gs ogs wg h Hinv hm
    · rw [if_neg hm] at Holen'
      have hlen : so'.len ≠ so.len := by intro he; rw [he] at Hol'; word
      rw [show addConfigL ogs h = ogs ++ [h] from if_neg hm, decide_eq_false hlen]
      have Hhb : Bounded h := (Hinv.1 h (by simp)).2
      unfold cfgOwn
      icases Hd with ⟨#Hdk, #Hdp⟩
      ihave %Hpl := ownSlice_len $$ Hdp
      wp_auto
      rename_i iu_ptr
      irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
      ihave HJ : (∃ (j iv : w64) (e0 : kvEntry) (sw' : GoSlice) (ncs : List kvConfig),
          "i" ∷ i_ptr ↦ j ∗ "Hiu" ∷ iu_ptr ↦ iv ∗ "e" ∷ e_ptr ↦ e0 ∗
          "work" ∷ work_ptr ↦ sw' ∗ "Hw" ∷ sw' ↦* (wc ++ ncs) ∗
          "Hwcap" ∷ ownSliceCap kvConfig sw' (DFrac.own 1) ∗
          "#Hn" ∷ ([∗list] c;g ∈ ncs;succsUpTo h (sint.nat j), cfgOwn c g) ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z d.pend'.len⌝ : IProp GF)
        $$ [i Hiu e work Hw Hwcap]
      · iexists W64 0, _, _, _, []
        rw [List.append_nil, show sint.nat (W64 0) = 0 from rfl]
        iframe
        isplitl []
        · unfold succsUpTo; simp only [List.range_zero, List.map_nil]
          iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
          iempintro
        ipureintro; word
      wp_for HJ
      wp_if_destruct
      · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z d.pend'.len := ⟨Hj.1, Hif⟩
        simp only [Hb', _root_.and_self, ↓reduceIte]
        list_elem h.pend (sint.nat j) as x
        wp_apply wp_load_slice_index d.pend' (sint.Z j) h.pend DFrac.discard x Hj.1 $$ [Hdp] as _
        · isplit
          · iexact Hdp
          · ipureintro; exact Hx_lookup
        wp_apply wp_set d.kv' h.kv DFrac.discard x.key' x.val' $$ [$Hdk] as %nk ⟨-, Hnk, -⟩
        · ipureintro; unfold Bounded at Hhb; omega
        ipersist Hnk
        wp_apply wp_removeAt d.pend' h.pend DFrac.discard j $$ [$Hdp] as %np ⟨-, Hnp, -⟩
        · ipureintro; exact Hb'
        ipersist Hnp
        wp_apply wp_slice_literal (l := [(⟨nk, np⟩ : kvConfig)])
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hl1, _⟩
        wp_apply wp_slice_append $$ [$Hw $Hwcap $Hl1] as %sw'' ⟨Hw, Hwcap, -⟩
        wp_for_post
        iframe
        iexists j + W64 1, _, _, sw'', ncs ++ [⟨nk, np⟩]
        rw [List.append_assoc]
        iframe
        have hsucc : succAt h (sint.nat j) = ⟨setL h.kv x.key' x.val', removeAtL h.pend (sint.nat j)⟩ := by
          have hx : pendAt h (sint.nat j) = x := by
            rw [pendAt_eq h _ (by word)]
            exact Option.some.inj ((List.getElem?_eq_getElem (by word)).symm.trans Hx_lookup)
          simp only [succAt, hx]
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, succsUpTo_succ, hsucc]
        isplitl []
        · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ c g => cfgOwn (GF := GF) c g)).2
          isplit
          · iexact Hn
          · unfold cfgOwn
            isplit
            · iexact Hnk
            · iexact Hnp
        ipureintro; word
      · -- the inner loop's end: `h` is in `out`, its successors in `work`
        have hj : sint.nat j = h.pend.length := by word
        rw [hj]
        wp_for_post
        iframe
        iexists so', sw', ocs', wc ++ ncs, ogs ++ [h], wg ++ succsUpTo h h.pend.length
        iframe
        isplitl []
        · iexact Hocs'
        unfold cfgOwn
        isplitl []
        · iapply (BigSepL2.bigSepL2_append
            (Φ := fun _ (c : kvConfig) (g : GCfg) =>
              iprop(c.kv' ↦*□ g.kv ∗ c.pend' ↦*□ g.pend : IProp GF))
            (Or.inl (by omega))).2
          isplit
          · iexact Hwc
          · iexact Hn
        ipureintro; exact cloInv_add gs ogs wg h Hinv hm
  · have Hz : ¬ 0 < sint.Z sw.len := by
      have h0 : sint.Z (W64 0) = 0 := rfl
      rw [h0] at Hif; exact Hif
    have hw0 : wcs = [] := List.eq_nil_of_length_eq_zero (by word)
    have hg0 : wgs = [] := List.eq_nil_of_length_eq_zero (by rw [← Hwlen, hw0]; rfl)
    subst hg0
    obtain ⟨h1, h2, h3⟩ := cloInv_done gs ogs Hinv
    iapply HΦ
    iframe
    isplitl []
    · iexact Hocs
    ipureintro; exact ⟨h1, h2, h3⟩

end proof

end linkv
end EtcdGrove
end Perennial
