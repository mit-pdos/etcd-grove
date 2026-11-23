module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.Nil
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.Concat
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.ScanPure
public import Perennial.Proof.encoding.binary.Results

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [TH : TreemapHyp GF]

omit [state.Assumptions] in
/-- The stored values after a `PUT` of `sl` (holding `val`) at `k`. -/
theorem vals_put (M : GMap w64 GoSlice) (S : GMap w64 (List w8)) (k : w64) (sl : GoSlice)
    (val : List w8) :
    (□ (([∗map] k' ↦ s ∈ M, s ↦*□ ((S !! k').getD [])) ∗ sl ↦*□ val) : IProp GF) ⊢
      [∗map] k' ↦ s ∈ GMap.insert k sl M, s ↦*□ (((GMap.insert k val S) !! k').getD []) := by
  apply BigSepM.bigSepM_intro
  intro k' v hget
  change (GMap.insert k sl M) !! k' = some v at hget
  by_cases e : k = k'
  · subst e
    rw [GMap.lookup_insert] at hget; cases hget
    rw [GMap.lookup_insert, Option.getD_some]
    iintro #⟨-, Hv⟩
    iexact Hv
  · rw [GMap.lookup_insert_ne _ _ e] at hget
    rw [GMap.lookup_insert_ne _ _ e]
    iintro #⟨Hm, -⟩
    iapply (BigSepM.bigSepM_lookup (M := GMap w64) (m := M)
      (Φ := fun k' s => iprop(s ↦*□ ((S !! k').getD []))) (by exact hget))
    iexact Hm

omit [state.Assumptions] in
/-- The stored values of the found keys `fk` (all in the treemap). -/
theorem vals_found (M : GMap w64 GoSlice) (S : GMap w64 (List w8)) (fk : List w64)
    (hsub : ∀ k ∈ fk, M !! k ≠ none) :
    (□ ([∗map] k ↦ sl ∈ M, sl ↦*□ ((S !! k).getD [])) : IProp GF) ⊢
      [∗list] x ∈ fk.map (fun k => ((M !! k).getD default, (S !! k).getD [])), x.1 ↦*□ x.2 := by
  apply BigSepL.bigSepL_intro
  intro j x hx
  rw [List.getElem?_map] at hx
  cases hfj : fk[j]? with
  | none => rw [hfj] at hx; cases hx
  | some k =>
    rw [hfj] at hx; cases hx
    have hkM := hsub k (List.mem_of_getElem? hfj)
    obtain ⟨sl, hsl⟩ : ∃ sl, M !! k = some sl := by
      cases h : M !! k with
      | none => exact absurd h hkM
      | some sl => exact ⟨sl, rfl⟩
    simp only [hsl, Option.getD_some]
    iintro #H
    iapply (BigSepM.bigSepM_lookup (M := GMap w64) (m := M)
      (Φ := fun k' s => iprop(s ↦*□ ((S !! k').getD []))) (by exact hsl))
    iexact H

omit [state.Assumptions] in
/-- The stored values of the selected entries `es` (all in the treemap). -/
theorem vals_es (M : GMap w64 GoSlice) (S : GMap w64 (List w8)) (es : List (w64 × GoSlice))
    (hsub : ∀ e ∈ es, M !! e.1 = some e.2) :
    (□ ([∗map] k ↦ sl ∈ M, sl ↦*□ ((S !! k).getD [])) : IProp GF) ⊢
      [∗list] x ∈ es.map (fun e => (e.2, (S !! e.1).getD [])), x.1 ↦*□ x.2 := by
  apply BigSepL.bigSepL_intro
  intro j x hx
  rw [List.getElem?_map] at hx
  cases hfj : es[j]? with
  | none => rw [hfj] at hx; cases hx
  | some e =>
    rw [hfj] at hx; cases hx
    have hsl := hsub e (List.mem_of_getElem? hfj)
    iintro #H
    iapply (BigSepM.bigSepM_lookup (M := GMap w64) (m := M)
      (Φ := fun k' s => iprop(s ↦*□ ((S !! k').getD []))) (by exact hsl))
    iexact H

/-- The `SCAN` range test on a key. -/
def inRangeB (K hi k : w64) : Bool := decide (sint.Z K ≤ sint.Z k) && decide (sint.Z k ≤ sint.Z hi)

/-- `Execute`, for a `SCAN` whose result length fits in an `int` (`concat`'s `totalLen`). -/
theorem state.Command.Execute.wp_bounded (c : Loc) (dq : DFrac) (cv : state.Command) (wc : WCmd)
    (st : Loc) (S : GMap w64 (List w8)) (hscan : wc.op = opSCAN → 8 ≤ wc.val.length)
    (hb : wc.op = opSCAN → (execCmd S wc).2.length < 2 ^ 63) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      c ↦{dq} cv ∗ cmdOk cv wc ∗ isState st S }}
    (App (Val (c @!! go.GoType.PointerType state.Command.ty @!! go!"Execute")) (Val #st))
  {{ (ret : GoSlice), RET #ret; c ↦{dq} cv ∗ isState st (execCmd S wc).1 ∗
      ret ↦*□ (execCmd S wc).2 }} := by
  have hnil := state.NIL.spec_holds (GF := GF)
  unfold state.NIL.spec at hnil
  have hput := TH.Put_spec
  have hget := TH.Get_spec
  wp_start as ⟨Hc, #Hok, Hst⟩
  rw [isState_unseal]
  unfold isStateDef
  icases Hst with ⟨%mu, %store, %M, #Hst, #Hmu, Htm, %HMS, #Hvals⟩
  unfold cmdOk
  icases Hok with ⟨%Hop, #Hv⟩
  ihave %Hcn := typedPointsto_not_null _ _ _ $$ Hc
  iStructNamed Hc
  ihave #Hst' := Hst
  iStructNamedSuffix Hst' "s"
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_pures
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  wp_if_destruct
  · -- PUT
    wp_pures
    rw [show interface.mkOk state.Key.ty #cv.K' = keyIface cv.K' from rfl,
      show interface.mkOk state.Value.ty #cv.V' = valIface cv.V' from rfl]
    wp_apply hput store M cv.K' cv.V' $$ [$Htm] as Htm
    · iexact Hpkg
    wp_apply hnil as %r Hr
    ipersist Hr
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    have hex : execCmd S wc = (S.insert wc.key wc.val, []) := by
      unfold execCmd; rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [← Hop.1]; exact Hif))]
    rw [hex]
    iapply HΦ
    isplitl [Op K V]
    · iapply typedPointsto_combine _ _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    dsimp only
    isplitl [Htm]
    · iexists mu, store, GMap.insert cv.K' cv.V' M
      rw [Hop.2]
      iframe Htm
      isplitr
      · iexact Hst
      isplitr
      · iexact Hmu
      isplitr
      · ipureintro
        intro k
        simp only [GMap.lookup_insert_eq_iff]
        split <;> simp_all
      · iapply vals_put
        isplitr
        · iexact Hvals
        · iexact Hv
    · iexact Hr
  · have hp : wc.op ≠ opPUT := by rw [← Hop.1]; exact Hif
    wp_if_destruct
    · -- GET
      have hgt : wc.op = opGET := by rw [← Hop.1]; exact Hif
      have hex : execCmd S wc = (S, (S !! wc.key).getD []) := by
        unfold execCmd
        rw [ite_eq_right_of_eq_false _ _ (eq_false hp), ite_eq_left_of_eq_true _ _ (eq_true hgt)]
      wp_pures
      rw [show interface.mkOk state.Key.ty #cv.K' = keyIface cv.K' from rfl]
      wp_apply hget store M cv.K' $$ [$Htm] as %v %ok ⟨Htm, %Hvok⟩
      · iexact Hpkg
      rw [Hop.2] at Hvok
      cases hM : M !! wc.key with
      | none =>
        rw [hM] at Hvok
        obtain ⟨rfl, rfl⟩ := Hvok
        have hS : S !! wc.key = none := by
          have := HMS wc.key; rw [hM] at this
          cases h : S !! wc.key with
          | none => rfl
          | some _ => rw [h] at this; cases this
        wp_auto
        wp_apply hnil as %r Hr
        ipersist Hr
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
        · inext; itrivial
        rw [hex, hS, Option.getD_none]
        iapply HΦ
        isplitl [Op K V]
        · iapply typedPointsto_combine _ _ _ Hcn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        dsimp only
        isplitl [Htm]
        · iexists mu, store, M
          iframe Htm
          isplitr
          · iexact Hst
          isplitr
          · iexact Hmu
          isplitr
          · ipureintro; exact HMS
          · iexact Hvals
        · iexact Hr
      | some sl =>
        rw [hM] at Hvok
        obtain ⟨rfl, rfl⟩ := Hvok
        wp_auto
        ihave #Hsl := BigSepM.bigSepM_lookup (M := GMap w64) (m := M)
          (Φ := fun k' s => iprop(s ↦*□ ((S !! k').getD []))) (by exact hM) $$ Hvals
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
        · inext; itrivial
        rw [hex]
        iapply HΦ
        isplitl [Op K V]
        · iapply typedPointsto_combine _ _ _ Hcn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        dsimp only
        isplitl [Htm]
        · iexists mu, store, M
          iframe Htm
          isplitr
          · iexact Hst
          isplitr
          · iexact Hmu
          isplitr
          · ipureintro; exact HMS
          · iexact Hvals
        · iexact Hsl
    · have hng : wc.op ≠ opGET := by rw [← Hop.1]; exact Hif
      wp_if_destruct
      · -- SCAN
        have hsc : wc.op = opSCAN := by rw [← Hop.1]; exact Hif
        have hex : execCmd S wc = (S, ((rangeKeys wc).filterMap S.lookup).flatten) := by
          unfold execCmd
          rw [ite_eq_right_of_eq_false _ _ (eq_false hp), ite_eq_right_of_eq_false _ _ (eq_false hng),
            ite_eq_left_of_eq_true _ _ (eq_true hsc)]
        have h8 := hscan hsc
        have hbd := hb hsc
        rw [hex] at hbd
        wp_apply wp_slice_make2 (V := GoSlice) (W64 0) $$ [] as %fnd ⟨Hfnd, Hfcap⟩
        · ipureintro; decide
        ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
        · iPkgInit
        ihave #Hv8 : cv.V' ↦*□ (wc.val.take 8 ++ wc.val.drop 8) $$ []
        · rw [List.take_append_drop]; iexact Hv
        wp_apply encoding.binary.wp_LittleEndian_Uint64 cv.V' (wc.val.take 8) _ (wc.val.drop 8)
          (by simp; omega) $$ [$Hv8] as -
        ihave #Htmpkg : isPkgInit (PROP := IProp GF)
            pkg_id.github_com.emirpasic.gods.maps.treemap $$ []
        · iPkgInit
        rw [show ∀ x b, (RecV BAnon x b : val) = #(func.mk BAnon x b) from
          fun x b => by rw [go.intoVal_unfold GoFunc]]
        wp_apply TH.Select_spec store M _ (inRangeB wc.key (wc.key + leToU64 (wc.val.take 8)))
            iprop(c_ptr ↦ c ∗ structFieldRef state.Command go!"K" c ↦{dq} cv.K' ∗
              count_ptr ↦ leToU64 (wc.val.take 8)) ?hsel $$ [Htm c K count]
          as %m' ⟨Htm, ⟨c, K, count⟩, %M', Hm', %HM'⟩
        case hsel =>
          intro k sl
          wp_start as ⟨c, K, count⟩
          unfold keyIface
          wp_auto
          unfold inRangeB
          rw [← Hop.2]
          wp_if_destruct
          · simp only [Bool.true_and]
            iapply HΦ; iframe
          · simp only [Bool.false_and]
            iapply HΦ; iframe
        · iframe
        obtain ⟨hi, hhi⟩ : ∃ hi, wc.key + leToU64 (wc.val.take 8) = hi := ⟨_, rfl⟩
        rw [hhi] at HM'
        wp_apply TH.Iterator_spec m' M' $$ [$Hm'] as %itv ⟨%es, %Hes, Hit⟩
        ihave Hit := TH.iter_alloc it_ptr itv es $$ [$it $Hit]
        ihave L : (∃ (dn rest : List (w64 × GoSlice)) (cur : Option (w64 × GoSlice)) (fs : GoSlice),
            "Hit" ∷ TH.ownIter it_ptr rest cur ∗ "found" ∷ found_ptr ↦ fs ∗
            "Hfs" ∷ fs ↦* dn.map Prod.snd ∗ "Hfcap" ∷ ownSliceCap GoSlice fs (DFrac.own 1) ∗
            "%Hd" ∷ ⌜dn ++ rest = es⌝ : IProp GF) $$ [Hit found Hfnd Hfcap]
        · iexists [], es, none, fnd
          iframe
          ipureintro; rfl
        repeat (irename : (iprop("_" ∷ True) : IProp GF) => Hjunk; iclear Hjunk)
        wp_for L
        wp_apply TH.Next_spec it_ptr rest cur $$ [$Hit] as %bn Hn
        cases rest with
        | nil =>
          icases Hn with ⟨%hbn, Hit⟩
          subst hbn
          rw [if_neg (fun h => absurd (go.intoVal_inj (of_decide_eq_true h)) (by decide)),
            if_pos (decide_eq_true rfl)]
          have hdn : dn = es := by simpa using Hd
          subst hdn
          have hsub : ∀ e ∈ dn, M !! e.1 = some e.2 := by
            intro e he
            have h1 := (Hes.2 e.1 e.2).mp he
            rw [HM'] at h1
            split at h1
            · exact h1
            · cases h1
          ihave #Hvs := vals_es M S dn hsub $$ [Hvals]
          · iexact Hvals
          have hmem : ∀ k, k ∈ dn.map Prod.fst ↔
              (sint.Z wc.key ≤ sint.Z k ∧ sint.Z k ≤ sint.Z hi) ∧ (S.lookup k).isSome := by
            intro k
            rw [List.mem_map]
            constructor
            · rintro ⟨⟨k', sl⟩, he, rfl⟩
              have h1 := (Hes.2 k' sl).mp he
              rw [HM'] at h1
              unfold inRangeB at h1
              split at h1
              · rename_i hr
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
                refine ⟨hr, ?_⟩
                rw [← HMS]; exact Option.isSome_iff_exists.mpr ⟨_, h1⟩
              · cases h1
            · rintro ⟨hr, hs⟩
              rw [← HMS] at hs
              obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp hs
              refine ⟨(k, sl), (Hes.2 k sl).mpr ?_, rfl⟩
              rw [HM']
              unfold inRangeB
              simp only [decide_eq_true hr.1, decide_eq_true hr.2, Bool.and_self, ↓reduceIte]
              exact hsl
          have hres : (dn.map (fun e => (S !! e.1).getD [])).flatten =
              ((rangeKeys wc).filterMap S.lookup).flatten := by
            rw [rangeKeys_eq, hhi, ← scan_flatten_sorted S (dn.map Prod.fst) Hes.1 wc.key hi hmem,
              List.map_map]
            rfl
          have hfst : (dn.map (fun e => (e.2, (S !! e.1).getD []))).map Prod.fst = dn.map Prod.snd := by
            rw [List.map_map]; rfl
          have hsnd : (dn.map (fun e => (e.2, (S !! e.1).getD []))).map Prod.snd =
              dn.map (fun e => (S !! e.1).getD []) := by
            rw [List.map_map]; rfl
          have hsum : lensUpTo (dn.map (fun e => (e.2, (S !! e.1).getD [])))
              (dn.map (fun e => (e.2, (S !! e.1).getD []))).length < 2 ^ 63 := by
            rw [← flatten_take_length, List.take_length, hsnd, hres]; exact hbd
          rw [← hfst]
          wp_auto
          wp_apply state.wp_concat fs (DFrac.own 1) _ hsum $$ [$Hfs $Hvs] as %r ⟨Hfs, Hr⟩
          rw [hsnd, hres]
          ipersist Hr
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
          · inext; itrivial
          rw [hex]
          iapply HΦ
          isplitl [Op K V]
          · iapply typedPointsto_combine _ _ _ Hcn
            simp only [TypedPointsto.typedPointstoDef]
            iframe
          dsimp only
          isplitl [Htm]
          · iexists mu, store, M
            iframe Htm
            isplitr
            · iexact Hst
            isplitr
            · iexact Hmu
            isplitr
            · ipureintro; exact HMS
            · iexact Hvals
          · iexact Hr
        | cons e r =>
          obtain ⟨k, sl⟩ := e
          icases Hn with ⟨%hbn, Hit⟩
          subst hbn
          rw [if_pos (decide_eq_true rfl)]
          wp_apply TH.Value_spec it_ptr r k sl $$ [$Hit] as Hit
          wp_apply wp_slice_literal (V := GoSlice) [sl]
          isplitr
          · ipureintro; rfl
          iintro %tmp ⟨Htmp, -⟩
          wp_auto
          wp_apply wp_slice_append (V := GoSlice) $$ [$Hfs $Hfcap $Htmp] as %fs' ⟨Hfs, Hfcap, -⟩
          wp_for_post
          iframe
          iexists dn ++ [(k, sl)], r, some (k, sl), fs'
          rw [List.map_append]
          iframe
          ipureintro; rw [← Hd]; simp
      -- anything else (not `SCAN`)
      have hnsc : wc.op ≠ opSCAN := by rw [← Hop.1]; exact Hif
      have hex : execCmd S wc = (S, []) := by
        unfold execCmd
        rw [ite_eq_right_of_eq_false _ _ (eq_false hp), ite_eq_right_of_eq_false _ _ (eq_false hng),
          ite_eq_right_of_eq_false _ _ (eq_false hnsc)]
      wp_apply hnil as %r Hr
      ipersist Hr
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
      · inext; itrivial
      rw [hex]
      iapply HΦ
      isplitl [Op K V]
      · iapply typedPointsto_combine _ _ _ Hcn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      dsimp only
      isplitl [Htm]
      · iexists mu, store, M
        iframe Htm
        isplitr
        · iexact Hst
        isplitr
        · iexact Hmu
        isplitr
        · ipureintro; exact HMS
        · iexact Hvals
      · iexact Hr

theorem state.Command.Execute.spec_holds : state.Command.Execute.spec (GF := GF) :=
  fun c dq cv wc st S hscan hb => state.Command.Execute.wp_bounded c dq cv wc st S hscan hb

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
