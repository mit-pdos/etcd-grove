module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__list
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.keyInScope
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListReadConsistency
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__DeepCopyObject
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObjList
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__UpdateList
public import Spec.maps.Keys
public import Spec.k8s_io.apimachinery.pkg.api.meta.SetList
public import Spec.k8s_io.apiserver.pkg.storage.PrepareKey
public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ItemsRO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj ObjList Input labelSel fieldSel)

section pure
variable [GooseExts]

/-- `list`'s loop over the keys `ks` visited (in order). -/
def loopOfKeys (x : Input) (m : RM) (ks : List GoString) : ListModel.LState w8 Obj :=
  ListModel.loop (selOkL x) (limitN x)
    ((ks.filterMap fun k => (m.items !! k).map (k, ·)).filter fun ko =>
      keyInScopeL x.ListKey' x.Recursive' ko.1)

theorem loopOfKeys_sorted (x : Input) (m : RM) :
    loopOfKeys x m (sortedKeysL m.items) =
      ListModel.loop (selOkL x) (limitN x) (scopeR x.ListKey' x.Recursive' m) := rfl

theorem loopOfKeys_snoc (x : Input) (m : RM) (ks : List GoString) (k : GoString) (o : Obj)
    (ho : m.items !! k = some o) :
    loopOfKeys x m (ks ++ [k]) =
      if keyInScopeL x.ListKey' x.Recursive' k then
        ListModel.lstep (selOkL x) (limitN x) (loopOfKeys x m ks) (k, o)
      else loopOfKeys x m ks := by
  unfold loopOfKeys ListModel.loop
  simp only [List.filterMap_append, List.filter_append, List.foldl_append, List.filterMap_cons,
    List.filterMap_nil, ho, Option.map_some]
  split <;> simp_all

theorem loopOfKeys_le (x : Input) (m : RM) (ks : List GoString) :
    (loopOfKeys x m ks).items.length ≤ (loopOfKeys x m ks).total ∧
      (loopOfKeys x m ks).total ≤ ks.length := by
  constructor
  · exact foldl_items_le_total _ _ _ _ (by simp)
  · unfold loopOfKeys; rw [ListModel.loop_total]
    exact Nat.le_trans (List.length_filter_le _ _) (List.length_filterMap_le _ _)

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem getAttrs_ne_nil :
    functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs [] ≠ func.nil := by
  intro h
  have hu := FuncUnfold.func_unfold (f := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs)
    (type_args := [])
  rw [h, go.intoVal_unfold GoFunc] at hu
  simp [func.nil, github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs.impl] at hu

theorem Model.list.wp_proof
    (wp_PrepareKey : storage.PrepareKey.spec (GF := GF) (hG := hG))
    (wp_LRC : ListReadConsistency.spec (GF := GF) (hG := hG))
    (wp_keyInScope : keyInScope.spec (GF := GF) (hG := hG))
    (wp_DeepCopy : k8s_etcd3.Obj.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_Keys : maps.Keys.spec_objMap (GF := GF) (hG := hG))
    (wp_TooLarge : storage.NewTooLargeResourceVersionError.spec (GF := GF) (hG := hG))
    (wp_newObjList : k8s_etcd3.newObjList.spec (GF := GF) (hG := hG))
    (wp_SetList : meta.SetList.spec_objList (GF := GF) (hG := hG))
    (wp_UpdateList : k8s_etcd3.versioner.UpdateList.spec (GF := GF) (hG := hG))
    (wp_PCT : storage.PrepareContinueToken.spec (GF := GF) (hG := hG))
    (wp_SM : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_SE : storage.SelectionPredicate.Empty.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    Model.list.spec (GF := GF) (hG := hG) := by
  have wp_Matches := mlistMatches.wp_ok wp_SM wp_LM wp_LE wp_FM wp_FE wp_GA
  have wp_PrepareContinueToken :=
    mlistPCT.wp_ok wp_PCT wp_SM wp_SE wp_LM wp_LE wp_FM wp_FE wp_GA
  intro mp m x hrv hlim0 hlim
  wp_start as Hm
  unfold modelAt modelRep modelVal
  icases Hm with ⟨#Hinit, %il, %rl, %M, #Hp, #HI, #Hit, #HR⟩
  ihave #Hsel0 := predOk_driver wp_SM wp_SE wp_LM wp_LE wp_FM wp_FE wp_GA x $$ Hinit
  iStructNamed Hp
  wp_auto
  wp_apply wp_PrepareKey as %prep %err0 %Hpk
  cases hk : k8s.prepareKeyM [] x.ListKey' x.Recursive' with
  | none =>
    rw [hk] at Hpk
    obtain ⟨ii, rfl⟩ : ∃ ii, err0 = GoInterface.ok ii := by
      cases err0 with
      | nil => exact absurd rfl Hpk
      | ok ii => exact ⟨ii, rfl⟩
    wp_auto
    iapply HΦ
    have : rlistL x m = ⟨.nil, .other⟩ := by unfold rlistL; simp [hk]
    rw [this]
    unfold respRep errRep deepRO deepRep
    simp only
    ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
  | some prepared =>
    rw [hk] at Hpk
    obtain ⟨rfl, rfl⟩ := Hpk
    wp_auto
    wp_apply (wp_LRC x hrv) as %cs %rv %ck %err1 Hc
    · iframe #
    icases Hc with %Hc
    generalize hc : listConsL x = cd at Hc
    cases cd with
    | none =>
      obtain ⟨ii, rfl⟩ : ∃ ii, err1 = GoInterface.ok ii := by
        cases err1 with
        | nil => exact absurd rfl Hc
        | ok ii => exact ⟨ii, rfl⟩
      wp_auto
      iapply HΦ
      have : rlistL x m = ⟨.nil, .other⟩ := by unfold rlistL; simp [hk, hc]
      rw [this]
      unfold respRep errRep deepRO deepRep
      simp only
      ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
    | some cr =>
      obtain ⟨c0, r0⟩ := cr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Hc
      wp_auto
      have hP : (listOptsV x).Predicate' = predV x := rfl
      icases typedPointsto_not_null_dup _ _ _ $$ opts with ⟨opts, %Hon⟩
      iStructNamed opts
      isimp only [hP] at Predicate
      icases typedPointsto_not_null_dup _ _ _ $$ Predicate with ⟨Predicate, %Hpn⟩
      iStructNamed Predicate
      simp only [predV] at *
      -- the panics are not reached
      have hRV : (listOptsV x).ResourceVersion' = x.MinRV' := rfl
      have hRec : (listOptsV x).Recursive' = x.Recursive' := rfl
      have hRT : (listOptsV x).RecordTimestamps' = false := rfl
      isimp only [hRV] at ResourceVersion
      isimp only [hRec] at Recursive
      isimp only [hRT] at RecordTimestamps
      rw [decide_eq_false (show ¬ sint.Z x.Limit' < sint.Z (W64 0) by word)]
      wp_auto
      by_cases hlp : sint.Z (W64 0) < sint.Z x.Limit'
      rw [decide_eq_true hlp]; wp_auto; rw [decide_eq_false (hlim (by word))]; wp_auto
      clear hlp; refine ?kLim
      rotate_left
      rw [decide_eq_false hlp]; wp_auto
      clear hlp; exact ?kLim
      ihave Hpr : (opts_ptr.[k8s_io.apiserver.pkg.storage.ListOptions, go!"Predicate"] ↦ predV x :
          IProp GF) $$ [Label Field GetAttrs IndexLabels IndexFields Limit Continue
            AllowWatchBookmarks ShardSelector]
      · iapply typedPointsto_combine _ _ _ Hpn
        simp only [TypedPointsto.typedPointstoDef, predV]
        iframe
      iunfold k8s.selPredOk at Hsel0
      icases Hsel0 with ⟨%Hsh, #HM, #HE⟩
      isimp only [predV] at Hpr
      wp_apply HE $$ %(opts_ptr.[k8s_io.apiserver.pkg.storage.ListOptions, go!"Predicate"])
        %(DFrac.own 1) [Hpr] as Hpr
      · iexact Hpr
      iStructNamed Hpr
      iclear HE HM
      cases predEmptyL x
      simp only [Bool.not_true, Bool.not_false]; wp_auto
      (try rw [decide_eq_false getAttrs_ne_nil]); (try wp_auto)
      refine ?kEmp
      rotate_left
      simp only [Bool.not_true, Bool.not_false]; wp_auto
      (try rw [decide_eq_false getAttrs_ne_nil]); (try wp_auto)
      exact ?kEmp
      by_cases hlt : uint.Z m.rv < uint.Z rv
      · rw [decide_eq_true hlt]
        wp_auto
        wp_apply (wp_TooLarge rv m.rv (W64 0)) as %e ⟨Htl0, %l, %st, %dv, %Hst, #Hl, #Hd⟩
        ihave #Htl := Htl0 $$ %(by trivial)
        iapply HΦ
        have : rlistL x m = ⟨.nil, tooLargeE⟩ := by
          unfold rlistL; simp [hk, hc]; intro h; exfalso; word
        rw [this]
        unfold respRep deepRO deepRep tooLargeE
        simp only
        isplitr
        · ipureintro; trivial
        iapply errRep_tooLarge_of e l st dv Hst
        iframe Htl Hl Hd
      rw [decide_eq_false hlt]
      wp_auto
      wp_join at next with [rv s]
      · by_cases hEx : rconsStr c0 = go!"Exact"
        · rw [decide_eq_true hEx]; wp_auto
          rw [decide_eq_false (show ¬ uint.Z rv < uint.Z (0 : w64) by word)]; wp_auto
          wp_join_done
        · rw [decide_eq_false hEx]; wp_auto
          wp_join_done
      ihave %HszM := itemsRO_size_map M m.items $$ Hit
      wp_apply (wp_Keys il) as %f #Hf
      wp_apply Hf $$ %M %DFrac.discard [] [HI] %HszM as %sl %ks - Hs %Hks
      · iexact HI
      repeat (irename : ("_" ∷ True : IProp GF) => Htriv; iclear Htriv)
      ihave Hpr : (opts_ptr.[k8s_io.apiserver.pkg.storage.ListOptions, go!"Predicate"] ↦ predV x :
          IProp GF) $$ [Label Field GetAttrs IndexLabels IndexFields Limit Continue
            AllowWatchBookmarks ShardSelector]
      · iapply typedPointsto_combine _ _ _ Hpn
        simp only [TypedPointsto.typedPointstoDef, predV]
        iframe
      ihave %Hsl := ownSlice_len $$ Hs
      ihave %hdom := itemsRO_dom_all M m.items $$ Hit
      have hks : ks = sortedKeysL m.items :=
        sortedKeysL_unique m.items ks (fun k => by rw [Hks.1, hdom]) Hks.2
      ihave HL : (∃ (j : w64) (isl : GoSlice) (xs : List GoInterface) (kv : GoString),
          "i" ∷ i_ptr ↦ j ∗ "items" ∷ items_ptr ↦ isl ∗ "k" ∷ k_ptr ↦ kv ∗
          "Hisl" ∷ isl ↦* xs ∗ "Hcap" ∷ ownSliceCap GoInterface isl (DFrac.own 1) ∗
          "Hxs" ∷ ([∗list] y;o ∈ xs;(loopOfKeys x m (ks.take (sint.nat j))).items.reverse,
            deepRep (DFrac.own 1) y (.obj o)) ∗
          "lastKey" ∷ lastKey_ptr ↦ ((loopOfKeys x m (ks.take (sint.nat j))).last.getD []) ∗
          "hasMore" ∷ hasMore_ptr ↦ (loopOfKeys x m (ks.take (sint.nat j))).more ∗
          "totalCount" ∷ totalCount_ptr ↦
            W64 ((loopOfKeys x m (ks.take (sint.nat j))).total : Int) ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF)
          $$ [i items k lastKey hasMore totalCount]
      · iexists W64 0, slice.nil, [], (zero_val GoString)
        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero,
          show loopOfKeys x m [] = ⟨[], none, false, 0⟩ from rfl]
        simp only [List.reverse_nil]
        iframe
        isplitl
        · iapply ownSlice_nil
        isplitl
        · iapply ownSliceCap_nil
        isplitl
        · iapply BigSepL2.bigSepL2_nil.2
          itrivial
        ipureintro; refine ⟨by word, by word⟩
      wp_for HL
      wp_if_destruct
      · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, by first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)⟩
        simp only [Hb', _root_.and_self, ↓reduceIte]
        list_elem ks (sint.nat j) as kj
        wp_apply (wp_load_slice_index sl (sint.Z j) ks (DFrac.own 1) kj Hj.1) $$ [Hs] as Hs
        · isplit
          · iexact Hs
          · ipureintro; exact Hkj_lookup
        wp_apply wp_keyInScope
        have hkjM : (M !! kj).isSome := (Hks.1 kj).1 (List.mem_of_getElem? Hkj_lookup)
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hkjM
        icases itemsRO_lookup M m.items kj v hv $$ Hit with ⟨%p, %o, ⟨%ho, %hvp⟩, #Hpo⟩
        have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        have htake : ks.take (sint.nat j + 1) = ks.take (sint.nat j) ++ [kj] := by
          rw [List.take_add_one, Hkj_lookup]; rfl
        have hstep := loopOfKeys_snoc x m (ks.take (sint.nat j)) kj o ho
        rw [← htake] at hstep
        obtain ⟨hLi0, hLt0⟩ := loopOfKeys_le x m (ks.take (sint.nat j))
        have hLt0' : (loopOfKeys x m (ks.take (sint.nat j))).total ≤ sint.nat j := by
          have := List.length_take_le (sint.nat j) ks; omega
        obtain ⟨L0, hL0⟩ : ∃ L0, loopOfKeys x m (ks.take (sint.nat j)) = L0 := ⟨_, rfl⟩
        rw [hL0] at hstep hLi0 hLt0' ⊢
        ihave %Hxl := BigSepL2.bigSepL2_length $$ Hxs
        ihave %Hil := ownSlice_len $$ Hisl
        simp only [List.length_reverse] at Hxl
        cases hsc : keyInScopeL x.ListKey' x.Recursive' kj
        · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at hstep
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, isl, xs, kj
          rw [hj1, hstep]
          iframe
          ipureintro; refine ⟨by word, by word⟩
        · simp only [hsc, ↓reduceIte] at hstep
          (try wp_auto)
          have htot : W64 (L0.total : Int) + W64 1 = W64 ((L0.total + 1 : Nat) : Int) := by word
          rw [htot]
          wp_if_destruct
          · have hln : limitN x = (sint.Z x.Limit').toNat := by
              unfold limitN; rw [if_pos (by word)]
            wp_if_destruct
            · have hst : loopOfKeys x m (ks.take (sint.nat j + 1)) =
                  ⟨L0.items, L0.last, true, L0.total + 1⟩ := by
                have hf : 0 < limitN x ∧ limitN x ≤ L0.items.length := by
                  rw [hln]; word
                rw [hstep]; simp [ListModel.lstep, hf]
              (try wp_auto)
              wp_for_post
              iframe
              iexists j + W64 1, isl, xs, kj
              rw [hj1, hst]
              iframe
              ipureintro; refine ⟨by word, by word⟩
            · have hnf : ¬ (0 < limitN x ∧ limitN x ≤ L0.items.length) := by
                rw [hln]; word
              (try wp_auto)
              wp_apply (wp_map_lookup1 go.string k8s_io.apimachinery.pkg.runtime.Object.ty il M kj
                DFrac.discard) $$ HI as -
              rw [hv, Option.getD_some, hvp]
              (try wp_auto)
              wp_apply (wp_Matches _ x p o DFrac.discard) $$ [$Hinit $Hpr $Hpo] as ⟨Hpr, -⟩
              cases hsel : selOkL x o
              · have hst : loopOfKeys x m (ks.take (sint.nat j + 1)) =
                    ⟨L0.items, L0.last, L0.more, L0.total + 1⟩ := by
                  rw [hstep]; simp [ListModel.lstep, hnf, hsel]
                (try wp_auto)
                wp_for_post
                iframe
                iexists j + W64 1, isl, xs, kj
                rw [hj1, hst]
                iframe
                ipureintro; refine ⟨by word, by word⟩
              · have hst : loopOfKeys x m (ks.take (sint.nat j + 1)) =
                    ⟨o :: L0.items, some kj, L0.more, L0.total + 1⟩ := by
                  rw [hstep]; simp [ListModel.lstep, hnf, hsel]
                (try wp_auto)
                wp_apply (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %c ⟨-, Hc⟩
                · iexact Hpo
                (try wp_auto)
                wp_apply wp_slice_literal
                isplitr
                · ipureintro; rfl
                iintro %osl ⟨Hosl, -⟩
                (try wp_auto)
                wp_apply wp_slice_append $$ [$Hisl $Hcap $Hosl] as %isl' ⟨Hisl, Hcap, -⟩
                (try wp_auto)
                wp_for_post
                iframe
                iexists j + W64 1, isl', _, kj
                rw [hj1, hst]
                simp only [List.reverse_cons, Option.getD_some]
                iframe
                isplitl
                · iapply BigSepL2.bigSepL2_singleton.2
                  unfold deepRep
                  iexists c
                  iframe Hc
                  ipureintro; rfl
                ipureintro; refine ⟨by word, by word⟩
          · have hnf : ¬ (0 < limitN x ∧ limitN x ≤ L0.items.length) := by
              unfold limitN; rw [if_neg (by word)]; omega
            (try wp_auto)
            wp_apply (wp_map_lookup1 go.string k8s_io.apimachinery.pkg.runtime.Object.ty il M kj
              DFrac.discard) $$ HI as -
            rw [hv, Option.getD_some, hvp]
            (try wp_auto)
            wp_apply (wp_Matches _ x p o DFrac.discard) $$ [$Hinit $Hpr $Hpo] as ⟨Hpr, -⟩
            cases hsel : selOkL x o
            · have hst : loopOfKeys x m (ks.take (sint.nat j + 1)) =
                  ⟨L0.items, L0.last, L0.more, L0.total + 1⟩ := by
                rw [hstep]; simp [ListModel.lstep, hnf, hsel]
              (try wp_auto)
              wp_for_post
              iframe
              iexists j + W64 1, isl, xs, kj
              rw [hj1, hst]
              iframe
              ipureintro; refine ⟨by word, by word⟩
            · have hst : loopOfKeys x m (ks.take (sint.nat j + 1)) =
                  ⟨o :: L0.items, some kj, L0.more, L0.total + 1⟩ := by
                rw [hstep]; simp [ListModel.lstep, hnf, hsel]
              (try wp_auto)
              wp_apply (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %c ⟨-, Hc⟩
              · iexact Hpo
              (try wp_auto)
              wp_apply wp_slice_literal
              isplitr
              · ipureintro; rfl
              iintro %osl ⟨Hosl, -⟩
              (try wp_auto)
              wp_apply wp_slice_append $$ [$Hisl $Hcap $Hosl] as %isl' ⟨Hisl, Hcap, -⟩
              (try wp_auto)
              wp_for_post
              iframe
              iexists j + W64 1, isl', _, kj
              rw [hj1, hst]
              simp only [List.reverse_cons, Option.getD_some]
              iframe
              isplitl
              · iapply BigSepL2.bigSepL2_singleton.2
                unfold deepRep
                iexists c
                iframe Hc
                ipureintro; rfl
              ipureintro; refine ⟨by word, by word⟩
      · have hn : ¬ sint.Z j < sint.Z sl.len := by
          first
            | exact Hif
            | exact of_decide_eq_false (go.intoVal_inj Hif)
            | exact fun h => Hif (by rw [decide_eq_true h])
        have htake : ks.take (sint.nat j) = ks := List.take_of_length_le (by word)
        obtain ⟨hLi, hLt⟩ := loopOfKeys_le x m ks
        obtain ⟨L, hL⟩ : ∃ L, loopOfKeys x m ks = L := ⟨_, rfl⟩
        have hloop : ListModel.loop (selOkL x) (limitN x) (scopeR x.ListKey' x.Recursive' m) = L := by
          rw [← loopOfKeys_sorted, ← hks, hL]
        have hle : ¬ uint.nat m.rv < uint.nat rv := by word
        rw [htake, hL] at *
        rw [htake, hL]
        ihave Hopts : (opts_ptr ↦ listOptsV x : IProp GF) $$ [ResourceVersion ResourceVersionMatch
            Hpr Recursive ProgressNotify SendInitialEvents RecordTimestamps]
        · iapply typedPointsto_combine _ _ _ Hon
          simp only [TypedPointsto.typedPointstoDef, listOptsV]
          iframe
        (try rw [if_pos (by simp [decide_eq_false hn])])
        wp_auto
        wp_apply wp_PrepareContinueToken as %cont %rem %err3 Hct
        ihave Hcase : (⌜err3 ≠ GoInterface.nil ∧ rlistL x m = ⟨.nil, .other⟩⌝ ∨
            ∃ remV : Option w64, ⌜err3 = GoInterface.nil ∧
              rlistL x m = ⟨.list (some L.items.reverse) m.rv cont remV, .none⟩⌝ ∗
              k8s.remIs rem remV : IProp GF) $$ [Hct]
        · cases hmore : L.more
          · isimp only [Bool.false_eq_true, ↓reduceIte] at Hct
            icases Hct with %Hct
            obtain ⟨rfl, rfl, rfl⟩ := Hct
            iright; iexists none
            isplitr
            · ipureintro; refine ⟨rfl, ?_⟩
              simp [rlistL, hk, hc, hle, hloop, hmore]
            · unfold k8s.remIs; ipureintro; rfl
          · isimp only [↓reduceIte] at Hct
            cases henc : encOkL (L.last.getD [] ++ [W8 0]) prep
            · isimp only [Bool.false_eq_true, ↓reduceIte] at Hct
              icases Hct with %Hct
              ileft; ipureintro; refine ⟨Hct, ?_⟩
              simp [rlistL, hk, hc, hle, hloop, hmore]; exact henc
            · isimp only [↓reduceIte] at Hct
              icases Hct with ⟨%Hct, Hrem⟩
              obtain ⟨rfl, rfl⟩ := Hct
              cases hpe : predEmptyL x
              · isimp only [Bool.false_eq_true, ↓reduceIte] at Hrem
                icases Hrem with %Hrem
                iright; iexists none
                isplitr
                · ipureintro; refine ⟨rfl, ?_⟩
                  simp [rlistL, hk, hc, hle, hloop, hmore, hpe]; exact henc
                · unfold k8s.remIs; ipureintro; exact Hrem
              · isimp only [↓reduceIte] at Hrem
                iright; iexists some (W64 (L.total : Int) - x.Limit')
                isplitr
                · ipureintro; refine ⟨rfl, ?_⟩
                  simp [rlistL, hk, hc, hle, hloop, hmore, hpe]; exact henc
                · unfold k8s.remIs; iexact Hrem
        icases Hcase with (%Hcase | ⟨%remV, %Hcase, Hrem⟩)
        · obtain ⟨hne, hr⟩ := Hcase
          obtain ⟨ii, rfl⟩ : ∃ ii, err3 = GoInterface.ok ii := by
            cases err3 with
            | nil => exact absurd rfl hne
            | ok ii => exact ⟨ii, rfl⟩
          wp_auto
          iapply HΦ
          rw [hr]
          unfold respRep errRep deepRO deepRep
          simp only
          ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
        obtain ⟨rfl, hr⟩ := Hcase
        wp_auto
        wp_apply +noauto wp_newObjList as %pl Hpl
        wp_auto
        imod ownSlice_persist _ _ _ $$ Hisl with #Hisl
        wp_apply (wp_SetList pl _ isl xs L.items.reverse DFrac.discard (DFrac.own 1))
          $$ [Hpl Hxs] as ⟨%sl', %Hsl', Hpl, Hsl'', -, -⟩
        · iframe Hpl Hxs Hisl
          try iPkgInit
        wp_auto
        icases typedPointsto_not_null_dup _ _ _ $$ Hpl with ⟨Hpl, %Hpln⟩
        iStructNamed Hpl
        wp_apply +noauto (wp_UpdateList pl 0 m.rv [] cont rem remV none) $$ [ResourceVersion Continue
            RemainingItemCount Hrem] as Hmeta
        · iframe Hrem
          try (isplitr; · iPkgInit)
          unfold k8s_etcd3.metaAtD
          iframe ResourceVersion Continue
          iexists null
          iframe RemainingItemCount
          unfold k8s.remIs; ipureintro; rfl
        unfold k8s_etcd3.metaAtD
        icases Hmeta with ⟨HRV, HC, %r, HR', Hr⟩
        ihave Hlist : (pl ↦ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.mk sl' m.rv cont r :
            IProp GF) $$ [Items HRV HC HR']
        · iapply typedPointsto_combine _ _ _ Hpln
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ipersist Hlist
        imod ownSlice_persist _ _ _ $$ Hsl'' with #Hsl''
        ihave Hr' : (|==> remRep (GF := GF) DFrac.discard r remV : IProp GF) $$ [Hr]
        · cases remV with
          | none => unfold k8s.remIs remRep; imodintro; iexact Hr
          | some n =>
            unfold k8s.remIs remRep
            ipersist Hr; imodintro; iexact Hr
        imod Hr' with #Hr'
        wp_auto
        iapply HΦ
        rw [hr]
        unfold respRep errRep deepRO deepRep itemsRep
        simp only
        isplitl
        · iexists pl, sl', r
          iframe Hlist Hsl'' Hr'
          ipureintro; exact ⟨rfl, Hsl'⟩
        · ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun

end proof

end k8s_correctness
end EtcdGrove
end Perennial
