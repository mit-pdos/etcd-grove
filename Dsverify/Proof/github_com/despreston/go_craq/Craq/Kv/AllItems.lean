/-
`(*KV).AllCommitted` and `(*KV).AllDirty`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.Lemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace kvp

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [store.kv.Assumptions] [store.Assumptions]

/-- The items found so far, as `itemsIn` wants them. -/
theorem itemsIn_of_list (l : List (Loc × (GoString × w64 × GoString × Bool))) :
    ([∗list] e ∈ l, itemPtr (hG := hG) e.1 e.2.1 e.2.2.1 e.2.2.2.1) ⊢
      [∗list] i ↦ p ∈ l.map Prod.fst, ∃ e, ⌜(l.map Prod.snd)[i]? = some e⌝ ∗
        itemPtr (hG := hG) p e.1 e.2.1 e.2.2.1 := by
  induction l with
  | nil =>
    simp only [List.map_nil]
    iintro -; iapply BigSepL.bigSepL_nil_intro (P := iprop(True)); itrivial
  | cons e l ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨He, H⟩
    simp only [List.map_cons]
    iapply BigSepL.bigSepL_cons.2
    isplitl [He]
    · iexists e.2
      iframe He
      ipureintro; rfl
    · ihave H := ih $$ H
      iapply (BigSepL.bigSepL_mono (fun _ => ?_)) $$ H
      simp only [List.getElem?_cons_succ]
      exact .rfl

theorem wp_AllCommitted (p : Loc) (γs : GName) :
    isKV (hG := hG) p γs ⊢
      <<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (Val #(methods (go.GoType.PointerType store.kv.KV.ty) go!"AllCommitted" #p))
          (Val #())) @ ∅
      <<{ storeOwn γs q S | (sl : GoSlice), RET (PairV #sl #interface.nil);
          itemsIn sl S (fun _ _ _ c => c = true) }>> := by
  iintro #Hkv
  unfold isKV
  icases Hkv with ⟨%mp, #Hitems, #Hmu, #Hpkg⟩
  unfold atomic_wp
  iintro %Φ AU
  wp_method_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  unfold lockInv
  icases Hi with ⟨%m, %S0, Hm, Hγ, %Hnone, Hmap⟩
  wp_apply wp_slice_literal (l := ([] : List Loc))
  isplitr
  · ipureintro; rfl
  iintro %kp ⟨Hout, Hocap⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoSlice) (fun _ (_ : Int) => iprop(
      ∃ (ns : GoSlice) (es : List (Loc × (GoString × w64 × GoString × Bool))) (fk : GoSlice),
        committed_ptr ↦ ns ∗ ns ↦* es.map Prod.fst ∗ ownSliceCap Loc ns (DFrac.own 1) ∗
        forKey_ptr ↦ fk ∗ ([∗list] e ∈ es, itemPtr e.1 e.2.1 e.2.2.1 e.2.2.2.1) ∗
        ⌜∀ e ∈ es, (e.2.2.1, e.2.2.2.1, e.2.2.2.2) ∈ S0.items e.2.1 ∧ e.2.2.2.2 = true⌝ ∗
        [∗map] k ↦ sl ∈ m, keyInv S0 k sl))) $$ Hm
  iintro %keys %hkeys
  isplitl [committed Hout Hocap forKey Hmap]
  · iexists _, [], _
    iframe
    simp only [List.map_nil]
    iframe
    isplitl []
    · iapply BigSepL.bigSepL_nil_intro (P := iprop(True)); itrivial
    · ipureintro; simp
  isplitl []
  · imodintro
    iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%ns, %es, %fk, Hc, Hns, Hnc, Hfk, Hes, %Hes, Hmap⟩
    wp_auto
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun k sl => keyInv (hG := hG) S0 k sl) hk2).1 $$ Hmap
      with ⟨Hk, Hmap⟩
    iunfold keyInv at Hk
    icases Hk with ⟨%l, Hk, %Hl⟩
    iunfold keyOwn at Hk
    icases Hk with ⟨Hsl, Hcap, Hits⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    simp only [List.length_map] at Hlen
    ihave HI : (∃ (j : w64) (pi : Loc) (ns' : GoSlice)
        (es' : List (Loc × (GoString × w64 × GoString × Bool))),
        "i" ∷ i_ptr ↦ j ∗ "item" ∷ item_ptr ↦ pi ∗ "Hc" ∷ committed_ptr ↦ ns' ∗
        "Hns" ∷ ns' ↦* es'.map Prod.fst ∗ "Hnc" ∷ ownSliceCap Loc ns' (DFrac.own 1) ∗
        "Hes" ∷ ([∗list] e ∈ es', itemPtr e.1 e.2.1 e.2.2.1 e.2.2.2.1) ∗
        "%Hes" ∷ ⌜∀ e ∈ es', (e.2.2.1, e.2.2.2.1, e.2.2.2.2) ∈ S0.items e.2.1 ∧ e.2.2.2.2 = true⌝ ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z v.len⌝ : IProp GF) $$ [i item Hc Hns Hnc Hes]
    · iexists W64 0, _, ns, es
      iframe
      ipureintro; exact ⟨Hes, by word⟩
    wp_for HI
    wp_if_destruct
    · -- loop body
      simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
      list_elem l (sint.nat j) as e
      wp_apply wp_load_slice_index v (sint.Z j) (l.map Prod.fst) _ e.1 Hj.1 $$ [Hsl] with Hsl
      · iframe; ipureintro
        rw [List.getElem?_map, show (sint.Z j).toNat = sint.nat j from rfl, He_lookup]; rfl
      icases BigSepL.bigSepL_lookup_acc He_lookup |>.1 $$ Hits with ⟨He, Hits⟩
      iunfold itemOwn at He
      iunfold itemPtr at He
      icases He with ⟨%Hnn, ⟨#HK, #HV, %vsl, #HVal, #Hx⟩, HC⟩
      have hmem : (e.2.1, e.2.2.1, e.2.2.2) ∈ S0.items key := by
        rw [Hl.2]; exact List.mem_map.2 ⟨e, List.mem_of_getElem? He_lookup, rfl⟩
      wp_auto
      ihave Hits := Hits $$ %e [HC]
      · unfold itemOwn itemPtr
        iframe HC HK HV
        isplitr
        · ipureintro; exact Hnn
        iexists vsl
        iframe #
      rw [list_set_lookup_self l _ e He_lookup]
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      obtain ⟨ep, ver, x, c⟩ := e
      cases c
      · wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, ep, ns', es'
        iframe
        ipureintro; exact ⟨Hes, by word⟩
      · wp_auto
        wp_apply wp_slice_literal (l := [ep])
        isplitr
        · ipureintro; rfl
        iintro %kp1 ⟨Htmp, -⟩
        wp_auto
        wp_apply wp_slice_append (V := Loc) $$ [$Hns $Hnc $Htmp] as %ns'' ⟨Hns, Hnc, -⟩
        ihave Hes : ([∗list] e ∈ es' ++ [(ep, (key, ver, x, true))],
            itemPtr (hG := hG) e.1 e.2.1 e.2.2.1 e.2.2.2.1) $$ [Hes]
        · iapply BigSepL.bigSepL_snoc.2
          iframe Hes
          unfold itemPtr
          iframe #
        wp_for_post
        iframe
        iexists j + W64 1, ep, ns'', es' ++ [(ep, (key, ver, x, true))]
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe
        · ipureintro
          refine ⟨?_, by word⟩
          intro e' he'
          rcases List.mem_append.1 he' with h | h
          · exact Hes e' h
          · simp only [List.mem_singleton] at h; subst h; exact ⟨hmem, rfl⟩
    · -- loop exit
      ihave Hmap := Hmap $$ [Hsl Hcap Hits]
      · unfold keyInv keyOwn
        iexists l
        iframe
        ipureintro; exact Hl
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists ns', es', v
      iframe
      ipureintro; exact Hes
  iintro ⟨%ns, %es, %fk, Hc, Hns, Hnc, Hfk, Hes, %Hes, Hmap⟩ Hm
  wp_auto
  iapply fupd_wp
  imod AU with ⟨%x', Hst, -, Hcommit⟩
  rcases x' with ⟨q, S', ⟨⟩⟩
  dsimp only [Tele.app]
  ihave %Heq := own_agree γs q S0 S' $$ Hγ Hst
  subst S'
  imod Hcommit $$ %() [Hst] with HΦ
  · iexact Hst
  imodintro
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hγ Hmap]
  · inext
    iexists m, S0
    iframe
    ipureintro; exact Hnone
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iapply HΦ
  unfold itemsIn
  iexists es.map Prod.fst, es.map Prod.snd
  iframe Hns
  isplitr
  · ipureintro
    refine ⟨by simp, ?_⟩
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact Hes e' he'
  · iapply itemsIn_of_list $$ Hes

theorem wp_AllDirty (p : Loc) (γs : GName) :
    isKV (hG := hG) p γs ⊢
      <<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (Val #(methods (go.GoType.PointerType store.kv.KV.ty) go!"AllDirty" #p))
          (Val #())) @ ∅
      <<{ storeOwn γs q S | (sl : GoSlice), RET (PairV #sl #interface.nil);
          itemsIn sl S (fun _ _ _ c => c = false) }>> := by
  iintro #Hkv
  unfold isKV
  icases Hkv with ⟨%mp, #Hitems, #Hmu, #Hpkg⟩
  unfold atomic_wp
  iintro %Φ AU
  wp_method_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  unfold lockInv
  icases Hi with ⟨%m, %S0, Hm, Hγ, %Hnone, Hmap⟩
  wp_apply wp_slice_literal (l := ([] : List Loc))
  isplitr
  · ipureintro; rfl
  iintro %kp ⟨Hout, Hocap⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoSlice) (fun _ (_ : Int) => iprop(
      ∃ (ns : GoSlice) (es : List (Loc × (GoString × w64 × GoString × Bool))) (fk : GoSlice),
        dirty_ptr ↦ ns ∗ ns ↦* es.map Prod.fst ∗ ownSliceCap Loc ns (DFrac.own 1) ∗
        forKey_ptr ↦ fk ∗ ([∗list] e ∈ es, itemPtr e.1 e.2.1 e.2.2.1 e.2.2.2.1) ∗
        ⌜∀ e ∈ es, (e.2.2.1, e.2.2.2.1, e.2.2.2.2) ∈ S0.items e.2.1 ∧ e.2.2.2.2 = false⌝ ∗
        [∗map] k ↦ sl ∈ m, keyInv S0 k sl))) $$ Hm
  iintro %keys %hkeys
  isplitl [dirty Hout Hocap forKey Hmap]
  · iexists _, [], _
    iframe
    simp only [List.map_nil]
    iframe
    isplitl []
    · iapply BigSepL.bigSepL_nil_intro (P := iprop(True)); itrivial
    · ipureintro; simp
  isplitl []
  · imodintro
    iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%ns, %es, %fk, Hc, Hns, Hnc, Hfk, Hes, %Hes, Hmap⟩
    wp_auto
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun k sl => keyInv (hG := hG) S0 k sl) hk2).1 $$ Hmap
      with ⟨Hk, Hmap⟩
    iunfold keyInv at Hk
    icases Hk with ⟨%l, Hk, %Hl⟩
    iunfold keyOwn at Hk
    icases Hk with ⟨Hsl, Hcap, Hits⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    simp only [List.length_map] at Hlen
    ihave HI : (∃ (j : w64) (pi : Loc) (ns' : GoSlice)
        (es' : List (Loc × (GoString × w64 × GoString × Bool))),
        "i" ∷ i_ptr ↦ j ∗ "item" ∷ item_ptr ↦ pi ∗ "Hc" ∷ dirty_ptr ↦ ns' ∗
        "Hns" ∷ ns' ↦* es'.map Prod.fst ∗ "Hnc" ∷ ownSliceCap Loc ns' (DFrac.own 1) ∗
        "Hes" ∷ ([∗list] e ∈ es', itemPtr e.1 e.2.1 e.2.2.1 e.2.2.2.1) ∗
        "%Hes" ∷ ⌜∀ e ∈ es', (e.2.2.1, e.2.2.2.1, e.2.2.2.2) ∈ S0.items e.2.1 ∧ e.2.2.2.2 = false⌝ ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z v.len⌝ : IProp GF) $$ [i item Hc Hns Hnc Hes]
    · iexists W64 0, _, ns, es
      iframe
      ipureintro; exact ⟨Hes, by word⟩
    wp_for HI
    wp_if_destruct
    · -- loop body
      simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
      list_elem l (sint.nat j) as e
      wp_apply wp_load_slice_index v (sint.Z j) (l.map Prod.fst) _ e.1 Hj.1 $$ [Hsl] with Hsl
      · iframe; ipureintro
        rw [List.getElem?_map, show (sint.Z j).toNat = sint.nat j from rfl, He_lookup]; rfl
      icases BigSepL.bigSepL_lookup_acc He_lookup |>.1 $$ Hits with ⟨He, Hits⟩
      iunfold itemOwn at He
      iunfold itemPtr at He
      icases He with ⟨%Hnn, ⟨#HK, #HV, %vsl, #HVal, #Hx⟩, HC⟩
      have hmem : (e.2.1, e.2.2.1, e.2.2.2) ∈ S0.items key := by
        rw [Hl.2]; exact List.mem_map.2 ⟨e, List.mem_of_getElem? He_lookup, rfl⟩
      wp_auto
      ihave Hits := Hits $$ %e [HC]
      · unfold itemOwn itemPtr
        iframe HC HK HV
        isplitr
        · ipureintro; exact Hnn
        iexists vsl
        iframe #
      rw [list_set_lookup_self l _ e He_lookup]
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      obtain ⟨ep, ver, x, c⟩ := e
      cases c
      · wp_auto
        wp_apply wp_slice_literal (l := [ep])
        isplitr
        · ipureintro; rfl
        iintro %kp1 ⟨Htmp, -⟩
        wp_auto
        wp_apply wp_slice_append (V := Loc) $$ [$Hns $Hnc $Htmp] as %ns'' ⟨Hns, Hnc, -⟩
        ihave Hes : ([∗list] e ∈ es' ++ [(ep, (key, ver, x, false))],
            itemPtr (hG := hG) e.1 e.2.1 e.2.2.1 e.2.2.2.1) $$ [Hes]
        · iapply BigSepL.bigSepL_snoc.2
          iframe Hes
          unfold itemPtr
          iframe #
        wp_for_post
        iframe
        iexists j + W64 1, ep, ns'', es' ++ [(ep, (key, ver, x, false))]
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe
        · ipureintro
          refine ⟨?_, by word⟩
          intro e' he'
          rcases List.mem_append.1 he' with h | h
          · exact Hes e' h
          · simp only [List.mem_singleton] at h; subst h; exact ⟨hmem, rfl⟩
      · wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, ep, ns', es'
        iframe
        ipureintro; exact ⟨Hes, by word⟩
    · -- loop exit
      ihave Hmap := Hmap $$ [Hsl Hcap Hits]
      · unfold keyInv keyOwn
        iexists l
        iframe
        ipureintro; exact Hl
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists ns', es', v
      iframe
      ipureintro; exact Hes
  iintro ⟨%ns, %es, %fk, Hc, Hns, Hnc, Hfk, Hes, %Hes, Hmap⟩ Hm
  wp_auto
  iapply fupd_wp
  imod AU with ⟨%x', Hst, -, Hcommit⟩
  rcases x' with ⟨q, S', ⟨⟩⟩
  dsimp only [Tele.app]
  ihave %Heq := own_agree γs q S0 S' $$ Hγ Hst
  subst S'
  imod Hcommit $$ %() [Hst] with HΦ
  · iexact Hst
  imodintro
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hγ Hmap]
  · inext
    iexists m, S0
    iframe
    ipureintro; exact Hnone
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iapply HΦ
  unfold itemsIn
  iexists es.map Prod.fst, es.map Prod.snd
  iframe Hns
  isplitr
  · ipureintro
    refine ⟨by simp, ?_⟩
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact Hes e' he'
  · iapply itemsIn_of_list $$ Hes

end proofs

end kvp

end github_com.despreston.go_craq

end Perennial
