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
open k8s_dist (targetL skipToL)

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

/-- `GoStep` in the lazy mode, when the lazy path has a successor. -/
theorem goStep_lazy (R : RevsL) (c : GCfg) (x : Input) (y : Output) (e : GCfg)
    (hne : stepL ⟨skipToL c.st (targetL x y (uint.nat c.st.st.rv)), c.pend⟩ x (plainOut y) ≠ []) :
    GoStep R 0 c x y e ↔
      e ∈ stepL ⟨skipToL c.st (targetL x y (uint.nat c.st.st.rv)), c.pend⟩ x (plainOut y) := by
  unfold GoStep; dsimp only
  split
  · exact Iff.rfl
  · next h => exact absurd ⟨rfl, hne⟩ h

/-- `GoStep` through `settle`, when the lazy path is not taken. -/
theorem goStep_settle (R : RevsL) (mode : Nat) (c : GCfg) (x : Input) (y : Output) (e : GCfg)
    (hn : ¬(mode = 0 ∧
      stepL ⟨skipToL c.st (targetL x y (uint.nat c.st.st.rv)), c.pend⟩ x (plainOut y) ≠ [])) :
    GoStep R mode c x y e ↔ ∃ d, GoSettle R (boundL x y) (mode = 2) x y c d ∧
      e ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x (plainOut y) := by
  unfold GoStep; dsimp only
  split
  · next h => exact absurd h hn
  · exact Iff.rfl

include sem package_sem in
/-- Porcupine's operation of `x` and `y`, decoded. -/
theorem decIO_box (x : Input) (y : Output) : decIO (boxIn x, boxOut y) = some (x, y) := by
  have h : ∃ p : Input × Output, (boxIn x, boxOut y) = (boxIn p.1, boxOut p.2) := ⟨(x, y), rfl⟩
  unfold decIO
  simp only [h, ↓reduceDIte]
  have hs : (boxIn x, boxOut y) = (boxIn h.choose.1, boxOut h.choose.2) := h.choose_spec
  have h1 := (GoInterfaceOk.mk.inj (GoInterface.ok.inj (congrArg Prod.fst hs))).2
  have h2 := (GoInterfaceOk.mk.inj (GoInterface.ok.inj (congrArg Prod.snd hs))).2
  have e : h.choose = (x, y) :=
    Prod.ext (Input_intoVal_inj (sem := sem) (package_sem := package_sem) h1).symm
      (Output_intoVal_inj (sem := sem) (package_sem := package_sem) h2).symm
  rw [e]

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

set_option maxHeartbeats 3200000 in
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
      ihave %Hcrv : ⌜c.st'.rv' = g.st.st.rv⌝ $$ [Hc]
      · iunfold cfgOwn at Hc
        icases Hc with ⟨Hst, -⟩
        iunfold storeOwn at Hst
        icases Hst with ⟨-, %h⟩
        ipureintro; exact h
      have Hfull : decide (mode = W64 2) = decide (uint.nat mode = 2) := by
        by_cases h2 : mode = W64 2
        · subst h2; rfl
        · rw [decide_eq_false h2, decide_eq_false]; intro h; apply h2; word
      by_cases hm : mode = W64 0
      rw [show decide (mode = W64 0) = true from decide_eq_true hm]
      wp_pures
      wp_auto
      wp_apply wp_target x y c.st'.rv' as %t %Ht
      have Ht' : uint.nat t = targetL x y (uint.nat g.st.st.rv) := by rw [Ht, Hcrv]
      have Htl := targetL_lt x y (uint.nat g.st.st.rv) Hxy
      (try wp_auto)
      wp_apply wp_skipTo hhl c g t $$ [$Hhh $Hc] as %d #Hd
      · ipureintro; exact ⟨Hgb.1, by omega⟩
      have Hdb : SharedBounded g0.st.items.length k ⟨skipToL g.st (uint.nat t), g.pend⟩ := by
        rw [Ht']; exact sharedBounded_skipTo _ k _ g Htl Hgb
      (try wp_auto)
      wp_apply wp_stepIdx mml d _ x y $$ [$Hmemo $Hd] as %es %ecs ⟨Hes, Hecs⟩
      · ipureintro; exact sharedBounded_stepIdxOk x y _ k Hit0 Hk Hxy _ Hdb
      (try wp_auto)
      ihave %Hel := ownSlice_len $$ Hes
      ihave %Hel2 := BigSepL2.bigSepL2_length $$ Hecs
      wp_if_destruct
      · ihave HJ : (∃ (p : w64) (e0 : mcfg) (ngs' : List GCfg),
            "i" ∷ i_ptr ↦ p ∗ "e" ∷ e_ptr ↦ e0 ∗ "Hset" ∷ cfgSetOwn next_ptr hhl ngs' ∗
            "Hes" ∷ es ↦* ecs ∗
            "%Hp" ∷ ⌜0 ≤ sint.Z p ∧ sint.Z p ≤ sint.Z es.len ∧ ∀ e', e' ∈ ngs' ↔ e' ∈ ngs ∨
              e' ∈ (stepL ⟨skipToL g.st (uint.nat t), g.pend⟩ x (plainOut y)).take (sint.nat p)⌝ :
              IProp GF) $$ [i e Hset Hes]
        · iexists W64 0, _, ngs
          iframe
          ipureintro
          refine ⟨by word, by word, fun e' => by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
        wp_for HJ
        by_cases Hif2 : sint.Z p < sint.Z es.len
        · (try simp only [decide_eq_true Hif2, ↓reduceIte])
          (try simp only [eq_self_iff_true, decide_true, ↓reduceIte])
          wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
          have Hb2 : 0 ≤ sint.Z p ∧ sint.Z p < sint.Z es.len := ⟨Hp.1, Hif2⟩
          simp only [Hb2, _root_.and_self, ↓reduceIte]
          list_elem ecs (sint.nat p) as ce
          list_elem (stepL ⟨skipToL g.st (uint.nat t), g.pend⟩ x (plainOut y)) (sint.nat p) as ge
          wp_apply wp_load_slice_index es (sint.Z p) ecs _ ce Hp.1 $$ [Hes] as Hes
          · iframe; ipureintro; exact Hce_lookup
          ihave #Hce := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
            Hce_lookup Hge_lookup $$ Hecs
          wp_apply wp_add next_ptr hhl ngs' ce ge $$ [$Hhh $Hset $Hce] as %bb Hpost
          ihave Hpost' := cfgSet_add_post next_ptr hhl ngs' ge bb $$ Hpost
          icases Hpost' with ⟨%ngs2, Hset, %Hngs2⟩
          wp_for_post
          iframe
          iexists p + W64 1, _, ngs2
          iframe
          ipureintro
          refine ⟨by word, by word, fun e' => ?_⟩
          rw [show sint.nat (p + W64 1) = sint.nat p + 1 by word, List.take_add_one, Hge_lookup,
            Hngs2, Hp.2.2]
          simp [or_assoc]
        · (try simp only [decide_eq_false Hif2, Bool.false_eq_true, ↓reduceIte])
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _, ngs'
          iframe
          ipureintro
          have Hpl : (stepL ⟨skipToL g.st (uint.nat t), g.pend⟩ x (plainOut y)).length ≤
              sint.nat p := by
            rw [← Hel2, Hel.1]
            have := Hp.2.1
            word
          refine ⟨by word, by word, fun e' => ?_⟩
          rw [Htake, Hp.2.2, Hj.2.2, List.take_of_length_le Hpl, Ht',
            show uint.nat mode = 0 by rw [hm]; rfl, goStep_lazy]
          rw [← Ht']; intro h; rw [h] at Hel2
          have := Hel.1
          simp only [List.length_nil] at Hel2
          rw [Hel2] at this
          word
      have Hns : ¬(uint.nat mode = 0 ∧
          stepL ⟨skipToL g.st (targetL x y (uint.nat g.st.st.rv)), g.pend⟩ x (plainOut y) ≠ []) := by
        rintro ⟨-, h⟩; apply h; rw [← Ht']
        apply List.eq_nil_of_length_eq_zero
        rw [← Hel2, Hel.1]; word
      iclear Hes Hecs
      rotate_left
      have Hns : ¬(uint.nat mode = 0 ∧
          stepL ⟨skipToL g.st (targetL x y (uint.nat g.st.st.rv)), g.pend⟩ x (plainOut y) ≠ []) := by
        rintro ⟨h, -⟩; apply hm; word
      rw [show decide (mode = W64 0) = false from decide_eq_false hm]
      wp_pures
      all_goals
        (try wp_auto)
        wp_apply wp_settle hhl r R c g (boundL x y) (decide (mode = W64 2)) x y $$ [$Hhh $Hr $Hc]
          as %dsl %dcs %dgs ⟨Hds, Hdcs, %Hdg⟩
        · ipureintro; exact ⟨Hgb.1, sharedBounded_settleOk R y _ k Hit0 Hk HR Hxy.2 g Hgb⟩
        ihave %Hdl := ownSlice_len $$ Hds
        ihave %Hdl2 := BigSepL2.bigSepL2_length $$ Hdcs
        icases Hdcs with #Hdcs
        ihave HK : (∃ (m : w64) (d0 : mcfg) (ngs' : List GCfg),
            "i" ∷ i_ptr ↦ m ∗ "d" ∷ d_ptr ↦ d0 ∗ "Hset" ∷ cfgSetOwn next_ptr hhl ngs' ∗
            "Hds" ∷ dsl ↦* dcs ∗
            "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z dsl.len ∧ ∀ e', e' ∈ ngs' ↔ e' ∈ ngs ∨
              ∃ d ∈ dgs.take (sint.nat m),
                e' ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x (plainOut y)⌝ :
              IProp GF) $$ [i d Hset Hds]
        · iexists W64 0, _, ngs
          iframe
          ipureintro
          refine ⟨by word, by word, fun e' => by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
        wp_for HK
        by_cases Hif3 : sint.Z m < sint.Z dsl.len
        · (try simp only [decide_eq_true Hif3, ↓reduceIte])
          (try simp only [eq_self_iff_true, decide_true, ↓reduceIte])
          wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
          have Hb3 : 0 ≤ sint.Z m ∧ sint.Z m < sint.Z dsl.len := ⟨Hm.1, Hif3⟩
          simp only [Hb3, _root_.and_self, ↓reduceIte]
          list_elem dcs (sint.nat m) as dc
          list_elem dgs (sint.nat m) as dg
          wp_apply wp_load_slice_index dsl (sint.Z m) dcs _ dc Hm.1 $$ [Hds] as Hds
          · iframe; ipureintro; exact Hdc_lookup
          ihave #Hdc := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
            Hdc_lookup Hdg_lookup $$ Hdcs
          ihave %Hdrv : ⌜dc.st'.rv' = dg.st.st.rv⌝ $$ [Hdc]
          · iunfold cfgOwn at Hdc
            icases Hdc with ⟨Hst, -⟩
            iunfold storeOwn at Hst
            icases Hst with ⟨-, %h⟩
            ipureintro; exact h
          have Hdmem := List.mem_of_getElem? Hdg_lookup
          have Hdgb : SharedBounded g0.st.items.length k dg :=
            sharedBounded_settle R _ _ x y _ k Hk HR Hxy.2 ((Hdg.1 dg).1 Hdmem) Hgb
          (try wp_auto)
          wp_apply wp_target x y dc.st'.rv' as %t2 %Ht2
          have Ht2' : uint.nat t2 = targetL x y (uint.nat dg.st.st.rv) := by rw [Ht2, Hdrv]
          have Htl2 := targetL_lt x y (uint.nat dg.st.st.rv) Hxy
          (try wp_auto)
          wp_apply wp_skipTo hhl dc dg t2 $$ [$Hhh $Hdc] as %d2 #Hd2
          · ipureintro; exact ⟨Hdgb.1, by omega⟩
          have Hdb2 : SharedBounded g0.st.items.length k ⟨skipToL dg.st (uint.nat t2), dg.pend⟩ := by
            rw [Ht2']; exact sharedBounded_skipTo _ k _ dg Htl2 Hdgb
          (try wp_auto)
          wp_apply wp_stepIdx mml d2 _ x y $$ [$Hmemo $Hd2] as %es2 %ecs2 ⟨Hes2, Hecs2⟩
          · ipureintro; exact sharedBounded_stepIdxOk x y _ k Hit0 Hk Hxy _ Hdb2
          (try wp_auto)
          ihave %Hel3 := ownSlice_len $$ Hes2
          ihave %Hel4 := BigSepL2.bigSepL2_length $$ Hecs2
          ihave HJ : (∃ (p : w64) (e0 : mcfg) (ngs2 : List GCfg),
              "i" ∷ i_ptr ↦ p ∗ "e" ∷ e_ptr ↦ e0 ∗ "Hset" ∷ cfgSetOwn next_ptr hhl ngs2 ∗
              "Hes" ∷ es2 ↦* ecs2 ∗
              "%Hp" ∷ ⌜0 ≤ sint.Z p ∧ sint.Z p ≤ sint.Z es2.len ∧ ∀ e', e' ∈ ngs2 ↔ e' ∈ ngs' ∨
                e' ∈ (stepL ⟨skipToL dg.st (uint.nat t2), dg.pend⟩ x (plainOut y)).take (sint.nat p)⌝ :
                IProp GF) $$ [i e Hset Hes2]
          · iexists W64 0, _, ngs'
            iframe
            ipureintro
            refine ⟨by word, by word, fun e' => by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
          wp_for HJ
          by_cases Hif4 : sint.Z p < sint.Z es2.len
          · (try simp only [decide_eq_true Hif4, ↓reduceIte])
            (try simp only [eq_self_iff_true, decide_true, ↓reduceIte])
            wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
            have Hb4 : 0 ≤ sint.Z p ∧ sint.Z p < sint.Z es2.len := ⟨Hp.1, Hif4⟩
            simp only [Hb4, _root_.and_self, ↓reduceIte]
            list_elem ecs2 (sint.nat p) as ce
            list_elem (stepL ⟨skipToL dg.st (uint.nat t2), dg.pend⟩ x (plainOut y)) (sint.nat p) as ge
            wp_apply wp_load_slice_index es2 (sint.Z p) ecs2 _ ce Hp.1 $$ [Hes] as Hes
            · iframe; ipureintro; exact Hce_lookup
            ihave #Hce := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
              Hce_lookup Hge_lookup $$ Hecs2
            wp_apply wp_add next_ptr hhl ngs2 ce ge $$ [$Hhh $Hset $Hce] as %bb Hpost
            ihave Hpost' := cfgSet_add_post next_ptr hhl ngs2 ge bb $$ Hpost
            icases Hpost' with ⟨%ngs3, Hset, %Hngs3⟩
            wp_for_post
            iframe
            iexists p + W64 1, _, ngs3
            iframe
            ipureintro
            refine ⟨by word, by word, fun e' => ?_⟩
            rw [show sint.nat (p + W64 1) = sint.nat p + 1 by word, List.take_add_one, Hge_lookup,
              Hngs3, Hp.2.2]
            simp [or_assoc]
          · (try simp only [decide_eq_false Hif4, Bool.false_eq_true, ↓reduceIte])
            (try wp_auto)
            wp_for_post
            iframe
            iexists m + W64 1, _, ngs2
            iframe
            ipureintro
            have Hpl : (stepL ⟨skipToL dg.st (uint.nat t2), dg.pend⟩ x (plainOut y)).length ≤
                sint.nat p := by
              rw [← Hel4, Hel3.1]
              have := Hp.2.1
              word
            refine ⟨by word, by word, fun e' => ?_⟩
            rw [Hp.2.2, List.take_of_length_le Hpl, Hm.2.2,
              show sint.nat (m + W64 1) = sint.nat m + 1 by word, List.take_add_one, Hdg_lookup, Ht2']
            simp [or_assoc, or_and_right, exists_or]
        · (try simp only [decide_eq_false Hif3, Bool.false_eq_true, ↓reduceIte])
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _, ngs'
          iframe
          ipureintro
          have Hml : dgs.length ≤ sint.nat m := by
            rw [← Hdl2, Hdl.1]
            have := Hm.2.1
            word
          refine ⟨by word, by word, fun e' => ?_⟩
          rw [Htake, Hm.2.2, Hj.2.2, List.take_of_length_le Hml, goStep_settle _ _ _ _ _ _ Hns]
          refine or_congr_right ⟨fun ⟨d, hd, he⟩ => ⟨d, ?_, he⟩, fun ⟨d, hd, he⟩ => ⟨d, ?_, he⟩⟩
          · rw [← Hfull]; exact (Hdg.1 d).1 hd
          · exact (Hdg.1 d).2 (by rw [Hfull]; exact hd)
    · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte])
      iunfold cfgSetOwn at Hset
      icases Hset with ⟨%lsl, %mb, %ncs, %B, Hfh, Hfl, Hfb, Hncs, Hcap, #Hncg, %Hcsl, Hb⟩
      ihave %Hnl := ownSlice_len $$ Hncs
      ihave %Hnl2 := BigSepL2.bigSepL2_length $$ Hncg
      imod ownSlice_persist _ _ _ $$ Hncs with #Hncs
      (try wp_auto)
      have Hjl : gs.length ≤ sint.nat j := by
        rw [← Hlen, Hl.1]
        have := Hj.2.1
        word
      have HS' : ∀ e, (∃ c, S c ∧ GoStep R (uint.nat mode) c x y e) ↔ e ∈ ngs := by
        intro e; rw [Hj.2.2, List.take_of_length_le Hjl]; simp only [hok]
      classical
      have Hstep : (sharedM g0 R (uint.nat mode)).step S (boxIn x, boxOut y) =
          if ∃ e, ∃ c, S c ∧ GoStep R (uint.nat mode) c x y e then
            some (fun e => ∃ c, S c ∧ GoStep R (uint.nat mode) c x y e) else none := by
        unfold sharedM; dsimp only; rw [decIO_box (sem := sem) (package_sem := package_sem)]
      iapply HΦ'
      isplitr
      · iexact Hrep0
      rw [Hstep]
      by_cases hne : ngs = []
      · have hn : ¬∃ e, ∃ c, S c ∧ GoStep R (uint.nat mode) c x y e := fun ⟨e, he⟩ => by
          rw [HS', hne] at he; simp at he
        simp only [hn, ↓reduceIte]
        isplitr
        · ipureintro
          rw [hne, List.length_nil] at Hnl2
          rw [Hnl2] at Hnl
          rw [Option.isSome_none, decide_eq_false_iff_not]
          word
        · ipureintro; trivial
      · obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil ngs hne
        have hy : ∃ e, ∃ c, S c ∧ GoStep R (uint.nat mode) c x y e := ⟨e0, (HS' e0).2 he0⟩
        simp only [hy, ↓reduceIte]
        isplitr
        · ipureintro
          have : 0 < ngs.length := by
            cases ngs with
            | nil => exact absurd rfl hne
            | cons => simp
          rw [Option.isSome_some, decide_eq_true_iff]
          word
        · iunfold sharedRep
          iexists lsl, ncs, ngs
          isplitr
          · ipureintro
            refine ⟨rfl, HS', fun g' hg' => ?_⟩
            obtain ⟨c', hc', hgs'⟩ := (HS' g').2 hg'
            exact sharedBounded_goStep R _ _ k c' g' x y Hk HR Hxy (hbd c' ((hok c').1 hc')) hgs'
          isplitr
          · iexact Hncs
          · iexact Hncg
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
