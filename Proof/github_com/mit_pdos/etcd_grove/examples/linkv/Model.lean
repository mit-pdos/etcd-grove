/-
Lean-first (no Rocq counterpart).

The proof of `Model`: the three closures. `Init`'s state is one empty configuration
(`gok_init`). `Step` runs `step` on each configuration and `addConfig`s the results
(`stepAllL`), then `closure`; its result represents `post S i o` (`step_closure_ok`), or is empty
when the decoder rejects the operation (`step_closure_none`), so its verdict is `kvM`'s.
`Equal` compares the two lists configuration by configuration (`configEqual`): equal lists
represent one state.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.step
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.addConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.closure
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.configEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkv github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

include sem package_sem in
/-- `Step`'s verdict and next state, from `closure`'s result `out` on `stepAllL gs x y`. -/
theorem step_result (gs out : List GCfg) (S : KVSet GoString GoString) (x : Input) (y : Output)
    (hS : GOk gs S) (hc : ClosureOk (stepAllL gs x y) out) (hcl : GClosed out) :
    ((kvM decOp).step S (boxIn x, boxOut y)).isSome = decide (out ≠ []) ∧
    ∀ S', (kvM decOp).step S (boxIn x, boxOut y) = some S' → GOk out S' := by
  have hstep : (kvM decOp).step S (boxIn x, boxOut y) = (decIO x y).bind (kvSeq.step S) := by
    simp only [kvM, decOp_box (sem := sem) (package_sem := package_sem)]
  rw [hstep]
  cases hd : decIO x y with
  | none =>
    have := step_closure_none gs out x y hd hc
    subst this
    simp
  | some io =>
    obtain ⟨i, o⟩ := io
    have hok := step_closure_ok gs out S x y i o hS hd hc hcl
    have hpost : post S i o = setOf out := hok.2
    simp only [Option.bind_some]
    refine ⟨?_, ?_⟩
    · simp only [kvSeq]
      split
      · next h =>
        rw [hpost] at h
        simp [(setOf_nonempty out).1 h]
      · next h =>
        have : ¬ out ≠ [] := fun hne => h (hpost ▸ (setOf_nonempty out).2 hne)
        simp only [Option.isSome_none]
        exact (decide_eq_false this).symm
    · intro S' h
      rw [kvSeq_step_some h]
      exact hok

theorem Model.wp_proof (wp_step : step.spec (GF := GF) (hG := hG))
    (wp_addConfig : addConfig.spec (GF := GF) (hG := hG))
    (wp_closure : closure.spec (GF := GF) (hG := hG))
    (wp_configEqual : configEqual.spec (GF := GF) (hG := hG)) :
    Model.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpecB
    iintro !> %Φ' _ HΦ'
    wp_auto
    wp_apply wp_slice_literal (V := kvConfig) (l := [zero_val kvConfig])
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl, _⟩
    ipersist Hsl
    wp_auto
    iapply HΦ'
    unfold stRepB
    iexists _, [zero_val kvConfig], [⟨[], []⟩]
    isplitr
    · ipureintro
      exact ⟨rfl, gok_init, fun g hg => by
        simp only [List.mem_singleton] at hg; subst hg; simp [Bounded]⟩
    isplitr
    · iexact Hsl
    iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
    unfold cfgOwn
    ihave Hn := ownSlice_nil (V := kvEntry) (GF := GF) DFrac.discard
    isplit
    · iexact Hn
    · iexact Hn
  isplitr
  · ipureintro; exact ⟨trivial, nofun⟩
  isplitr
  · -- Step
    unfold stepSpecB
    simp only [linkvS, stRepB]
    iintro %n %v %S %i %o
    iintro !> %Φ' ⟨%Hn, #Hrep, %Hio⟩ HΦ'
    obtain ⟨x, y, rfl, rfl⟩ := Hio
    icases Hrep with ⟨%sl, %cs, %gs, ⟨%hv, %hok, %hbd⟩, #Hs, #Hcs⟩
    subst hv
    ihave %Hl := ownSlice_len $$ Hs
    ihave %Hlen := BigSepL2.bigSepL2_length $$ Hcs
    wp_auto
    wp_apply wp_slice_literal (V := kvConfig) (l := [])
    isplitr
    · ipureintro; rfl
    iintro %nsl ⟨Hn0, Hn0cap⟩
    wp_auto
    irename : (in_ptr ↦ x : IProp GF) => Hin
    ihave HI : (∃ (j : w64) (c0 : kvConfig) (sn : GoSlice) (ncs : List kvConfig),
        "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ c0 ∗ "next" ∷ next_ptr ↦ sn ∗ "Hn" ∷ sn ↦* ncs ∗
        "Hncap" ∷ ownSliceCap kvConfig sn (DFrac.own 1) ∗
        "#Hncs" ∷ ([∗list] c;g ∈ ncs;(gs.take (sint.nat j)).foldl (stepOneL x y) [], cfgOwn c g) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF)
      $$ [i c next Hn0 Hn0cap]
    · iexists W64 0, _, _, []
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
      iframe
      isplitl []
      · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
        iempintro
      ipureintro; word
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
      simp only [Hb', _root_.and_self, ↓reduceIte]
      list_elem cs (sint.nat j) as c
      list_elem gs (sint.nat j) as g
      wp_apply wp_load_slice_index sl (sint.Z j) cs _ c Hj.1 $$ [Hs] as -
      · isplit
        · iexact Hs
        · ipureintro; exact Hc_lookup
      ihave #Hc := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
        Hc_lookup Hg_lookup $$ Hcs
      have Hgb : Bounded n g := hbd g (List.mem_of_getElem? Hg_lookup)
      wp_apply wp_step c g x y $$ [$Hc] as %r %rcs ⟨Hr, #Hrcs⟩
      · ipureintro; unfold Bounded at Hgb; constructor <;> omega
      ihave %Hrl := ownSlice_len $$ Hr
      ihave %Hrlen := BigSepL2.bigSepL2_length $$ Hrcs
      have Htake : (gs.take (sint.nat (j + W64 1))).foldl (stepOneL x y) [] =
          stepOneL x y ((gs.take (sint.nat j)).foldl (stepOneL x y) []) g := by
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hg_lookup]
        simp
      generalize (gs.take (sint.nat j)).foldl (stepOneL x y) [] = acc at Htake ⊢
      ihave HJ : (∃ (k : w64) (d0 : kvConfig) (sn' : GoSlice) (ncs' : List kvConfig),
          "i" ∷ i_ptr ↦ k ∗ "d" ∷ d_ptr ↦ d0 ∗ "next" ∷ next_ptr ↦ sn' ∗ "Hn" ∷ sn' ↦* ncs' ∗
          "Hncap" ∷ ownSliceCap kvConfig sn' (DFrac.own 1) ∗
          "#Hncs" ∷ ([∗list] c;g ∈ ncs';((stepL g x y).take (sint.nat k)).foldl addConfigL acc,
            cfgOwn c g) ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z r.len⌝ : IProp GF)
        $$ [i d next Hn Hncap]
      · iexists W64 0, _, _, ncs
        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
        iframe
        isplitl []
        · iexact Hncs
        ipureintro; word
      wp_for HJ
      wp_if_destruct
      · have Hk' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z r.len := ⟨Hk.1, Hif⟩
        simp only [Hk', _root_.and_self, ↓reduceIte]
        list_elem rcs (sint.nat k) as d
        list_elem (stepL g x y) (sint.nat k) as g'
        wp_apply wp_load_slice_index r (sint.Z k) rcs _ d Hk.1 $$ [Hr] as Hr
        · iframe; ipureintro; exact Hd_lookup
        ihave #Hd := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
          Hd_lookup Hg'_lookup $$ Hrcs
        wp_apply wp_addConfig sn' ncs' _ d g' $$ [$Hn $Hncap $Hncs $Hd] as %sn'' %ncs'' ⟨Hn, Hncap, #Hncs'⟩
        wp_for_post
        iframe
        iexists k + W64 1, _, sn'', ncs''
        iframe
        rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one, Hg'_lookup]
        simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
        isplitl []
        · iexact Hncs'
        ipureintro; word
      · -- the inner loop's end: `stepOneL` of `g`
        have hall : (stepL g x y).take (sint.nat k) = stepL g x y :=
          List.take_of_length_le (by word)
        rw [hall] at *
        wp_for_post
        iframe
        iexists j + W64 1, _, sn', ncs'
        iframe
        rw [Htake, stepOneL]
        isplitl []
        · iexact Hncs
        ipureintro; word
    · -- `closure` of the configurations' steps
      have hall : gs.take (sint.nat j) = gs := List.take_of_length_le (by word)
      rw [hall, show gs.foldl (stepOneL x y) [] = stepAllL gs x y from rfl]
      have hb1 : ∀ g' ∈ stepAllL gs x y, Bounded (n + 1) g' := by
        intro g' hg'
        obtain ⟨g, hg, hs⟩ := (mem_stepAllL gs x y g').1 hg'
        exact stepL_bounded n g x y (hbd g hg) g' hs
      wp_apply +noauto wp_closure sn ncs (stepAllL gs x y) (DFrac.own 1) (n + 1) $$ [$Hn $Hncs]
        as %out %ocs %ogs ⟨-, Hout, -, #Hocs, %Hco⟩
      · ipureintro; exact ⟨by omega, hb1⟩
      ipersist Hout
      obtain ⟨hc, hcl, hob⟩ := Hco
      obtain ⟨hres1, hres2⟩ := step_result (sem := sem) (package_sem := package_sem) gs ogs S x y hok hc hcl
      ihave %Hol := ownSlice_len $$ Hout
      ihave %Holen := BigSepL2.bigSepL2_length $$ Hocs
      wp_auto
      iapply HΦ'
      isplitl []
      · ipureintro
        rw [hres1]
        have h0 : sint.Z (W64 0) = 0 := rfl
        rw [h0]
        have hlenO : ogs.length = sint.nat out.len := by rw [← Holen]; exact Hol.1
        by_cases he : ogs = []
        · subst he
          have : sint.Z out.len = 0 := by
            simp only [List.length_nil] at hlenO; have := Hol.2; word
          simp [this]
        · have : 0 < sint.Z out.len := by
            have := List.length_pos_iff.2 he
            have := Hol.2
            word
          simp [he, this]
      cases hst : (kvM decOp).step S (boxIn x, boxOut y) with
      | none => itrivial
      | some S' =>
        simp only
        iexists out, ocs, ogs
        isplitl []
        · ipureintro; exact ⟨rfl, hres2 S' hst, hob⟩
        isplit
        · iexact Hout
        · iexact Hocs
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal
    unfold equalSpec
    simp only [linkvS]
    iintro %v %w %s %t
    iintro !> %Φ' ⟨#Hv, #Hw⟩ HΦ'
    unfold stRep
    icases Hv with ⟨%sla, %csa, %gsa, ⟨%hva, %hoka⟩, #Hsa, #Hcsa⟩
    icases Hw with ⟨%slb, %csb, %gsb, ⟨%hvb, %hokb⟩, #Hsb, #Hcsb⟩
    subst hva hvb
    ihave %Hla := ownSlice_len $$ Hsa
    ihave %Hlb := ownSlice_len $$ Hsb
    ihave %Hlena := BigSepL2.bigSepL2_length $$ Hcsa
    ihave %Hlenb := BigSepL2.bigSepL2_length $$ Hcsb
    wp_auto
    wp_if_destruct
    · rename_i iu_ptr
      have Heq := Hif; clear Hif
      irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
      ihave HI : (∃ (k j : w64),
          "i" ∷ i_ptr ↦ k ∗ "Hiu" ∷ iu_ptr ↦ j ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sla.len ∧
            gsa.take (sint.nat k) = gsb.take (sint.nat k)⌝ : IProp GF) $$ [i Hiu]
      · iexists W64 0, _
        iframe
        ipureintro; refine ⟨by word, by word, rfl⟩
      wp_for HI
      wp_if_destruct
      · have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sla.len := ⟨Hk.1, Hif⟩
        have Hb2' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z slb.len := by rw [← Heq]; exact Hb'
        simp only [Hb', _root_.and_self, ↓reduceIte]
        list_elem csa (sint.nat k) as ca
        list_elem gsa (sint.nat k) as ga
        list_elem csb (sint.nat k) as cb
        list_elem gsb (sint.nat k) as gb
        wp_apply wp_load_slice_index sla (sint.Z k) csa _ ca Hk.1 $$ [Hsa] as _
        · isplit
          · iexact Hsa
          · ipureintro; exact Hca_lookup
        rw [if_pos Hb']
        wp_apply wp_load_slice_index sla (sint.Z k) csa _ ca Hk.1 $$ [Hsa] as _
        · isplit
          · iexact Hsa
          · ipureintro; exact Hca_lookup
        simp only [Hb2', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index slb (sint.Z k) csb _ cb Hk.1 $$ [Hsb] as _
        · isplit
          · iexact Hsb
          · ipureintro; exact Hcb_lookup
        ihave #Hca := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
          Hca_lookup Hga_lookup $$ Hcsa
        ihave #Hcb := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
          Hcb_lookup Hgb_lookup $$ Hcsb
        wp_apply wp_configEqual ca cb ga gb $$ [$Hca $Hcb]
        cases hab : decide (ga = gb)
        · -- different: `false`
          wp_auto
          wp_for_post
          iapply HΦ'
          isplitl []
          · iexists sla, csa, gsa
            isplitl []
            · ipureintro; exact ⟨rfl, hoka⟩
            isplit
            · iexact Hsa
            · iexact Hcsa
          isplitl []
          · iexists slb, csb, gsb
            isplitl []
            · ipureintro; exact ⟨rfl, hokb⟩
            isplit
            · iexact Hsb
            · iexact Hcsb
          ipureintro; nofun
        · wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one,
            List.take_add_one, Hk.2.2, Hga_lookup, Hgb_lookup, of_decide_eq_true hab]
      · -- all equal: `true`, one state
        have h1 : gsa.length = sint.nat k := by word
        have h2 : gsb.length = sint.nat k := by rw [← Hlenb, Hlb.1, ← Heq]; word
        have heq : gsa = gsb := by
          have := Hk.2.2
          rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
        iapply HΦ'
        isplitl []
        · iexists sla, csa, gsa
          isplitl []
          · ipureintro; exact ⟨rfl, hoka⟩
          isplit
          · iexact Hsa
          · iexact Hcsa
        isplitl []
        · iexists slb, csb, gsb
          isplitl []
          · ipureintro; exact ⟨rfl, hokb⟩
          isplit
          · iexact Hsb
          · iexact Hcsb
        ipureintro
        intro _
        rw [hoka.2, hokb.2, heq]
    · -- different lengths: `false`
      iapply HΦ'
      isplitl []
      · iexists sla, csa, gsa
        isplitl []
        · ipureintro; exact ⟨rfl, hoka⟩
        isplit
        · iexact Hsa
        · iexact Hcsa
      isplitl []
      · iexists slb, csb, gsb
        isplitl []
        · ipureintro; exact ⟨rfl, hokb⟩
        isplit
        · iexact Hsb
        · iexact Hcsb
      ipureintro; nofun
  ileft
  ipureintro; trivial

end proof

end linkv
end EtcdGrove
end Perennial
