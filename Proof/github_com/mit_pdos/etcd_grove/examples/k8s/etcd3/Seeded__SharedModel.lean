/-
Lean-first (no Rocq counterpart).

The proof of `Seeded.SharedModel(revs, mode)` (k8s-dist K9 step 4, `notes/k8s-dist-k9.md` §2.1): the
three closures over a fresh `histHashes` and `wmemo`. `Init`'s state is the seeded configuration.
`Step` adds to a `cfgSet` every configuration `GoStep` reaches from each of the state's (the lazy
path's `stepIdx` results, or `settle`'s configurations skipped to their target and stepped), so its
list holds exactly `sharedM`'s next state, each `SharedBounded` one more (`sharedBounded_goStep`).
`Equal` compares the two lists configuration by configuration: one history pointer
(`histOwn_agree_len`), `storeEqual`, `pendEqual`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Seeded__SharedModel
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__canonical
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__skipTo
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.target
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.bound
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.stepIdx
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.settle
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cfgSet__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pendEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine (initSpec stepSpec equalSpec isEqHash stepPost)
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem gcfg_eq (a b : GCfg) (h1 : a.st.hist = b.st.hist) (h2 : a.st.st = b.st.st)
    (h3 : a.pend = b.pend) : a = b := by
  obtain ⟨⟨s1, hi1⟩, p1⟩ := a
  obtain ⟨⟨s2, hi2⟩, p2⟩ := b
  simp_all

/-- `cfgSet.add`'s result, either way: the set holds what it held and `g`. -/
theorem cfgSet_add_post (s hh : Loc) (gs : List GCfg) (g : GCfg) (b : Bool) :
    (if b then cfgSetOwn (GF := GF) s hh (gs ++ [g]) else cfgSetOwn s hh gs ∗ ⌜g ∈ gs⌝) ⊢
      ∃ gs', cfgSetOwn (GF := GF) s hh gs' ∗ ⌜∀ e, e ∈ gs' ↔ e ∈ gs ∨ e = g⌝ := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H, %h⟩
    iexists gs
    iframe
    ipureintro
    intro e
    constructor
    · exact Or.inl
    · rintro (h' | rfl)
      · exact h'
      · exact h
  · simp only [↓reduceIte]
    iintro H
    iexists gs ++ [g]
    iframe
    ipureintro
    intro e
    simp

theorem Seeded.SharedModel.wp_proof (wp_histOf : histOf.spec (GF := GF) (hG := hG))
    (wp_canonical : histHashes.canonical.spec (GF := GF) (hG := hG))
    (wp_skipTo : histHashes.skipTo.spec (GF := GF) (hG := hG))
    (wp_target : target.spec (GF := GF) (hG := hG))
    (wp_bound : bound.spec (GF := GF) (hG := hG))
    (wp_stepIdx : stepIdx.spec (GF := GF) (hG := hG))
    (wp_settle : settle.spec (GF := GF) (hG := hG))
    (wp_add : cfgSet.add.spec (GF := GF) (hG := hG))
    (wp_storeEqual : storeEqual.spec (GF := GF) (hG := hG))
    (wp_pendEqual : pendEqual.spec (GF := GF) (hG := hG)) :
    Seeded.SharedModel.spec (GF := GF) (hG := hG) := by
  intro s hs g0 r R mode
  wp_start as ⟨#Hs0, #Hh0, #Hhs, #Hr, %Hpre⟩
  obtain ⟨Hwf0, Hrv0, Hit0, HR⟩ := Hpre
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  generalize «$r0_ptr» = hhl at *
  iStructNamed «$r0»
  imod sync.init_Mutex (hhInv (GF := GF) hhl) ⊤ (structFieldRef histHashes go!"mu" hhl)
    $$ mu [canon «is» gaps] with #Hhhm
  · inext
    iunfold hhInv
    isplitl [canon «is»]
    · iunfold hhCanon
      iexists map.nil, map.nil, ∅, ∅
      iframe
      ileft; ipureintro; exact ⟨rfl, rfl⟩
    · iunfold hhGaps
      iexists map.nil, ∅
      iframe
      ileft; ipureintro; rfl
  ihave #Hhh : hhOwn (GF := GF) hhl $$ []
  · iunfold hhOwn; isplit
    · iexact Psync
    · iexact Hhhm
  iclear Hhhm
  wp_apply (wp_map_make1 (K := wkey) (V := Bool)) as %mm Hmm
  generalize «$r0_ptr» = mml at *
  iStructNamed «$r0»
  imod sync.init_Mutex (wmemoInv (GF := GF) mml) ⊤ (structFieldRef wmemo go!"mu" mml)
    $$ mu [m Hmm] with #Hmmm
  · inext
    iunfold wmemoInv
    iexists mm, ∅
    iframe
    iapply BigSepM.bigSepM_empty.2
    iempintro
  ihave #Hmemo : memoOwn (GF := GF) mml $$ []
  · iunfold memoOwn; isplit
    · iexact Psync
    · iexact Hmmm
  iclear Hmmm
  ipersist hh
  ipersist memo
  iStructNamed s
  ipersist st0
  ipersist h0
  ipersist mode
  ipersist revs
  ipersist full
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
    simp only [sharedS]
    iintro !> %Φ' _ HΦ'
    wp_auto
    wp_apply wp_histOf s.h0' hs g0.hist DFrac.discard $$ [$Hh0 $Hhs] as %h ⟨-, #Hhl⟩
    have Hlen0 : g0.hist.length < 2 ^ 64 := by have := Hwf0.1; omega
    wp_apply wp_canonical hhl h g0.hist $$ [$Hhh $Hhl] as %hc #Hhc
    · ipureintro; exact Hlen0
    (try wp_auto)
    wp_apply wp_slice_literal (V := mcfg) (l := [(⟨s.st0', slice.nil, hc⟩ : mcfg)])
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl, _⟩
    ipersist Hsl
    wp_auto
    iapply HΦ'
    unfold sharedRep
    iexists _, [(⟨s.st0', slice.nil, hc⟩ : mcfg)], [(⟨g0, []⟩ : GCfg)]
    isplitr
    · ipureintro
      refine ⟨rfl, fun g => by simp [sharedM], fun g hg => ?_⟩
      simp only [List.mem_singleton] at hg; subst hg
      exact ⟨Hwf0, nofun, by simp, by simp; omega, by simp⟩
    isplitr
    · iexact Hsl
    iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
    unfold cfgOwn
    ihave Hn2 := ownSlice_nil (V := Input) (GF := GF) DFrac.discard
    isplit
    · iexact Hs0
    isplit
    · iexact Hhc
    isplit
    · iexact Hn2
    · ipureintro; exact Hlen0
  isplitr
  · ipureintro; exact ⟨trivial, nofun⟩
  isplitr
  · -- Step
    unfold stepSpec
    (try unfold stepPost)
    simp only [sharedS]
    iintro %k %v %S %i %o
    iintro !> %Φ' ⟨%Hk, #Hrep, #Hio⟩ HΦ'
    ihave #Hrep0 := Hrep
    iunfold sharedRep at Hrep
    icases Hio with ⟨%x, %y, %Hxy⟩
    obtain ⟨rfl, rfl, Hxy⟩ := Hxy
    icases Hrep with ⟨%sl, %cs, %gs, ⟨%hv, %hok, %hbd⟩, #Hs, #Hcs⟩
    subst hv
    ihave %Hl := ownSlice_len $$ Hs
    ihave %Hlen := BigSepL2.bigSepL2_length $$ Hcs
    wp_auto
    wp_apply wp_bound x y
    iStructNamed next
    irename : ("_" ∷ True : IProp GF) => Hjunk
    iclear Hjunk
    ihave Hset : cfgSetOwn (GF := GF) next_ptr hhl [] $$ [hh list buckets]
    · iunfold cfgSetOwn
      iexists slice.nil, map.nil, [], ∅
      iframe
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      isplitl
      · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
        iempintro
      isplitl
      · ipureintro; simp
      ileft
      ipureintro; exact ⟨rfl, rfl⟩
    irename : (in_ptr ↦ x : IProp GF) => Hin
    ihave HI : (∃ (j : w64) (c0 : mcfg) (ngs : List GCfg),
        "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ c0 ∗ "Hset" ∷ cfgSetOwn next_ptr hhl ngs ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
          ∀ e, e ∈ ngs ↔ ∃ c ∈ gs.take (sint.nat j), GoStep R (uint.nat mode) c x y e⌝ : IProp GF)
      $$ [i c Hset]
    · iexists W64 0, _, []
      iframe
      ipureintro; refine ⟨by word, by word, fun e => by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
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
      have Hgb := hbd g (List.mem_of_getElem? Hg_lookup)
      have Htake : ∀ e, (∃ c ∈ gs.take (sint.nat (j + W64 1)), GoStep R (uint.nat mode) c x y e) ↔
          (∃ c ∈ gs.take (sint.nat j), GoStep R (uint.nat mode) c x y e) ∨
            GoStep R (uint.nat mode) g x y e := by
        intro e
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hg_lookup]
        simp [or_and_right, exists_or]
      sorry
    · sorry
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal
    unfold equalSpec
    simp only [sharedS]
    iintro %ka %kb %v %w %sa %sb
    iintro !> %Φ' ⟨#Hv, #Hw⟩ HΦ'
    ihave #Hv0 := Hv
    ihave #Hw0 := Hw
    iunfold sharedRep at Hv Hw
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
        ihave #Hca := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
          Hca_lookup Hga_lookup $$ Hcsa
        ihave #Hcb := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
          Hcb_lookup Hgb_lookup $$ Hcsb
        icases ownSlice_elem_acc (sint.Z k) ca sla DFrac.discard csa Hk.1 Hca_lookup $$ Hsa with ⟨#Hela, -⟩
        icases ownSlice_elem_acc (sint.Z k) cb slb DFrac.discard csb Hk.1 Hcb_lookup $$ Hsb with ⟨#Helb, -⟩
        iStructNamed Hela
        iStructNamed Helb
        wp_auto
        (try simp only [Hb', _root_.and_self, ite_true])
        (try wp_auto)
        (try simp only [Hb2', _root_.and_self, ite_true])
        (try wp_auto)
        iunfold cfgOwn at Hca Hcb
        icases Hca with ⟨#Hsta, #Hha, #Hpa, %Hla'⟩
        icases Hcb with ⟨#Hstb, #Hhb, #Hpb, %Hlb'⟩
        by_cases hhe : ca.hist' = cb.hist'
        · rw [decide_eq_true hhe]
          wp_auto
          (try simp only [Hb', _root_.and_self, ite_true])
          (try wp_auto)
          (try simp only [Hb2', _root_.and_self, ite_true])
          (try wp_auto)
          wp_apply wp_storeEqual ca.st' cb.st' ga.st.st gb.st.st $$ [$Hsta $Hstb]
          cases hse : decide (ga.st.st = gb.st.st)
          · wp_auto
            wp_for_post
            iapply HΦ'
            isplitl []
            · iexact Hv0
            isplitl []
            · iexact Hw0
            ipureintro; nofun
          · wp_auto
            (try simp only [Hb', _root_.and_self, ite_true])
            (try wp_auto)
            (try simp only [Hb2', _root_.and_self, ite_true])
            (try wp_auto)
            wp_apply wp_pendEqual ca.pend' cb.pend' ga.pend gb.pend $$ [$Hpa $Hpb]
            cases hpe : decide (ga.pend = gb.pend)
            · wp_auto
              wp_for_post
              iapply HΦ'
              isplitl []
              · iexact Hv0
              isplitl []
              · iexact Hw0
              ipureintro; nofun
            · rw [hhe]
              icases histOwn_agree_len _ _ _ Hla' Hlb' $$ Hha Hhb with %hhq
              have hgeq : ga = gb := gcfg_eq ga gb hhq (of_decide_eq_true hse) (of_decide_eq_true hpe)
              wp_auto
              wp_for_post
              iframe
              iexists k + W64 1, _
              iframe
              ipureintro
              refine ⟨by word, by word, ?_⟩
              rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one,
                List.take_add_one, Hk.2.2, Hga_lookup, Hgb_lookup, hgeq]
        · rw [decide_eq_false hhe]
          wp_auto
          wp_for_post
          iapply HΦ'
          isplitl []
          · iexact Hv0
          isplitl []
          · iexact Hw0
          ipureintro; nofun
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
        funext g
        apply propext
        rw [hoka g, hokb g, heq]
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

end k8s_etcd3
end EtcdGrove
end Perennial
