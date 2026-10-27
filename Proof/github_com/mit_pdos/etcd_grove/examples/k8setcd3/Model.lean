/-
Lean-first (no Rocq counterpart).

The proof of `Model(st0)`: the three closures. `Init`'s state is one configuration, the seeded
store (`gok_init`). `Step` runs `step` on each configuration and `addConfig`s the results
(`stepAllL`), then `closure`; its result represents `ppost S x (ansOf y)` (`step_closure_ok`), so
its verdict is `pM (kSpec g0) decOp`'s (`step_result`). `Equal` compares the two lists
configuration by configuration (`configEqual`): equal lists represent one state.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.step
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.addConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.closure
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.configEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine (initSpec stepSpec equalSpec isEqHash stepPost)
open github_com.mit_pdos.etcd_grove.examples.k8setcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

include sem package_sem in
/-- `Step`'s verdict and next state, from `closure`'s result `out` on `stepAllL gs x y`. -/
theorem step_result (g0 : GSt) (gs out : List GCfg) (S : linkv.PSet GSt Input) (x : Input)
    (y : Output) (hS : GOk g0 gs S) (hc : ClosureOk g0 (stepAllL gs x y) out)
    (hcl : GClosed g0 out) :
    ((linkv.pM (kSpec g0) decOp).step S (boxIn x, boxOut y)).isSome = decide (out ≠ []) ∧
    ∀ S', (linkv.pM (kSpec g0) decOp).step S (boxIn x, boxOut y) = some S' → GOk g0 out S' := by
  rw [linkv.pM_step (kSpec g0) decOp S _ x (ansOf y)
    (decOp_box (sem := sem) (package_sem := package_sem) x y)]
  have hok := step_closure_ok g0 gs out S x y hS hc hcl
  have hpost : linkv.ppost (kSpec g0) S x (ansOf y) = setOf out := hok.2
  refine ⟨?_, ?_⟩
  · simp only [linkv.pSeq]
    split
    · next h =>
      rw [hpost] at h
      simp [(setOf_nonempty out).1 h]
    · next h =>
      have : ¬ out ≠ [] := fun hne => h (hpost ▸ (setOf_nonempty out).2 hne)
      simp only [Option.isSome_none]
      exact (decide_eq_false this).symm
  · intro S' h
    rw [linkv.pSeq_step_some h]
    exact hok

theorem Model.wp_proof (wp_step : step.spec (GF := GF) (hG := hG))
    (wp_addConfig : addConfig.spec (GF := GF) (hG := hG))
    (wp_closure : closure.spec (GF := GF) (hG := hG))
    (wp_configEqual : configEqual.spec (GF := GF) (hG := hG)) :
    Model.spec (GF := GF) (hG := hG) := by
  intro s0 g0
  wp_start as ⟨#Hs0, %Hlen0⟩
  wp_auto
  ipersist st0
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpec
    simp only [k8setcd3S]
    iintro !> %Φ' _ HΦ'
    wp_auto
    wp_apply wp_slice_literal (V := mcfg) (l := [(⟨s0, slice.nil⟩ : mcfg)])
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl, _⟩
    ipersist Hsl
    wp_auto
    iapply HΦ'
    unfold stRepB
    iexists _, [(⟨s0, slice.nil⟩ : mcfg)], [gInit g0]
    isplitr
    · ipureintro
      exact ⟨rfl, gok_init g0, fun g hg => by
        simp only [List.mem_singleton] at hg; subst hg; simpa using bounded_gInit g0⟩
    isplitr
    · iexact Hsl
    iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
    unfold cfgOwn
    dsimp only [gInit]
    ihave Hn2 := ownSlice_nil (V := Input) (GF := GF) DFrac.discard
    isplit
    · iexact Hs0
    · iexact Hn2
  isplitr
  · ipureintro; exact ⟨trivial, nofun⟩
  isplitr
  · -- Step
    unfold stepSpec
    (try unfold stepPost)
    simp only [k8setcd3S]
    iintro %k %v %S %i %o
    iintro !> %Φ' ⟨%Hk, #Hrep, %Hio⟩ HΦ'
    have Hn : k + g0.items.length + 1 + 1 < 2 ^ 63 := by omega
    generalize hn : k + g0.items.length + 1 = n at Hn ⊢
    ihave #Hrep0 := Hrep
    iunfold stRepB at Hrep
    obtain ⟨x, y, rfl, rfl⟩ := Hio
    icases Hrep with ⟨%sl, %cs, %gs, ⟨%hv, %hok, %hbd⟩, #Hs, #Hcs⟩
    subst hv
    ihave %Hl := ownSlice_len $$ Hs
    ihave %Hlen := BigSepL2.bigSepL2_length $$ Hcs
    wp_auto
    wp_apply wp_slice_literal (V := mcfg) (l := [])
    isplitr
    · ipureintro; rfl
    iintro %nsl ⟨Hn0, Hn0cap⟩
    wp_auto
    irename : (in_ptr ↦ x : IProp GF) => Hin
    ihave HI : (∃ (j : w64) (c0 : mcfg) (sn : GoSlice) (ncs : List mcfg),
        "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ c0 ∗ "next" ∷ next_ptr ↦ sn ∗ "Hn" ∷ sn ↦* ncs ∗
        "Hncap" ∷ ownSliceCap mcfg sn (DFrac.own 1) ∗
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
    by_cases Hif : sint.Z j < sint.Z sl.len
    · (try simp only [decide_eq_true Hif, ↓reduceIte])
      (try simp only [eq_self_iff_true, decide_true, ↓reduceIte])
      wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
      have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
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
      · ipureintro
        unfold Bounded at Hgb
        constructor <;> omega
      ihave %Hrl := ownSlice_len $$ Hr
      ihave %Hrlen := BigSepL2.bigSepL2_length $$ Hrcs
      have Htake : (gs.take (sint.nat (j + W64 1))).foldl (stepOneL x y) [] =
          stepOneL x y ((gs.take (sint.nat j)).foldl (stepOneL x y) []) g := by
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hg_lookup]
        simp
      generalize (gs.take (sint.nat j)).foldl (stepOneL x y) [] = acc at Htake ⊢
      ihave HJ : (∃ (k : w64) (d0 : mcfg) (sn' : GoSlice) (ncs' : List mcfg),
          "i" ∷ i_ptr ↦ k ∗ "d" ∷ d_ptr ↦ d0 ∗ "next" ∷ next_ptr ↦ sn' ∗ "Hn" ∷ sn' ↦* ncs' ∗
          "Hncap" ∷ ownSliceCap mcfg sn' (DFrac.own 1) ∗
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
      by_cases Hif : sint.Z k < sint.Z r.len
      · (try simp only [decide_eq_true Hif, ↓reduceIte])
        (try simp only [eq_self_iff_true, decide_true, ↓reduceIte])
        wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
        have Hk' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z r.len := ⟨Hk.1, Hif⟩
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
        (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte])
        (try simp only [decide_eq_false false_neq_true, Bool.false_eq_true, ↓reduceIte]); wp_pures
        cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
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
      (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte])
      (try simp only [decide_eq_false false_neq_true, Bool.false_eq_true, ↓reduceIte]); wp_pures
      cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
      have hall : gs.take (sint.nat j) = gs := List.take_of_length_le (by word)
      rw [hall, show gs.foldl (stepOneL x y) [] = stepAllL gs x y from rfl]
      have hb1 : ∀ g' ∈ stepAllL gs x y, Bounded (n + 1) g' :=
        stepAllL_bounded n gs x y hbd
      wp_apply +noauto wp_closure g0 sn ncs (stepAllL gs x y) (DFrac.own 1) (n + 1) $$ [$Hn $Hncs]
        as %out %ocs %ogs ⟨-, Hout, -, #Hocs, %Hco⟩
      · ipureintro; exact ⟨by omega, hb1⟩
      ipersist Hout
      obtain ⟨hc, hcl, hob⟩ := Hco
      obtain ⟨hres1, hres2⟩ := step_result (sem := sem) (package_sem := package_sem) g0 gs ogs S x y hok hc hcl
      ihave %Hol := ownSlice_len $$ Hout
      ihave %Holen := BigSepL2.bigSepL2_length $$ Hocs
      wp_auto
      iapply HΦ'
      isplitl []
      · iexact Hrep0
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
      (try unfold github_com.anishathalye.porcupine.stepPost)
      (try simp only [github_com.anishathalye.porcupine.stepPost])
      cases hst : (linkv.pM (kSpec g0) decOp).step S (boxIn x, boxOut y) with
      | none => itrivial
      | some S' =>
        simp only [k8setcd3S]
        rw [show k + 1 + g0.items.length + 1 = n + 1 by omega]
        unfold stRepB
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
    simp only [k8setcd3S]
    iintro %ka %kb %v %w %s %t
    iintro !> %Φ' ⟨#Hv, #Hw⟩ HΦ'
    ihave #Hv0 := Hv
    ihave #Hw0 := Hw
    iunfold stRepB at Hv Hw
    icases Hv with ⟨%sla, %csa, %gsa, ⟨%hva, %hoka, -⟩, #Hsa, #Hcsa⟩
    icases Hw with ⟨%slb, %csb, %gsb, ⟨%hvb, %hokb, -⟩, #Hsb, #Hcsb⟩
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
      by_cases Hif : sint.Z k < sint.Z sla.len
      · (try simp only [decide_eq_true Hif, ↓reduceIte])
        (try simp only [eq_self_iff_true, decide_true, ↓reduceIte])
        wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
        have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sla.len := ⟨Hk.1, Hif⟩
        have Hb2' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z slb.len := by rw [← Heq]; exact Hb'
        (try simp only [Hb', _root_.and_self, ↓reduceIte])
        (try simp only [decide_true, eq_self_iff_true, ↓reduceIte])
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
          · iexact Hv0
          isplitl []
          · iexact Hw0
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
        (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte])
        (try simp only [decide_eq_false false_neq_true, Bool.false_eq_true, ↓reduceIte]); wp_pures
        cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
        have h1 : gsa.length = sint.nat k := by word
        have h2 : gsb.length = sint.nat k := by rw [← Hlenb, Hlb.1, ← Heq]; word
        have heq : gsa = gsb := by
          have := Hk.2.2
          rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
        (try simp only [decide_true, eq_self_iff_true, ↓reduceIte])
        (try wp_auto)
        iapply HΦ'
        isplitl []
        · iexact Hv0
        isplitl []
        · iexact Hw0
        ipureintro
        intro _
        rw [hoka.2, hokb.2, heq]
    · -- different lengths: `false`
      iapply HΦ'
      isplitl []
      · iexact Hv0
      isplitl []
      · iexact Hw0
      ipureintro; nofun
  ileft
  ipureintro; trivial

end proof

end k8setcd3
end EtcdGrove
end Perennial
