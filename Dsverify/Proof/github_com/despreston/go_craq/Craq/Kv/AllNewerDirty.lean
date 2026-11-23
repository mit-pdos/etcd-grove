/-
`(*KV).AllNewerDirty`.
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

/-- The accumulated items, in the indexed form of `itemsIn`. -/
theorem acc_idx (acc : List (Loc × (GoString × w64 × GoString × Bool))) :
    ([∗list] e ∈ acc, itemPtr (hG := hG) e.1 e.2.1 e.2.2.1 e.2.2.2.1) ⊢
      [∗list] i ↦ p ∈ acc.map Prod.fst, ∃ e, ⌜(acc.map Prod.snd)[i]? = some e⌝ ∗
        itemPtr (hG := hG) p e.1 e.2.1 e.2.2.1 := by
  induction acc with
  | nil =>
    iintro -
    simp only [List.map_nil]
    iapply BigSepL.bigSepL_nil_intro (P := iprop(True)); itrivial
  | cons a acc ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, H⟩
    simp only [List.map_cons]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · iexists a.2
      iframe Ha
      ipureintro
      simp
    · ihave H := ih $$ H
      iapply BigSepL.bigSepL_mono ?_ $$ H
      intro k x _
      iintro ⟨%e, %he, Hp⟩
      iexists e
      iframe Hp
      ipureintro
      simpa using he

theorem wp_AllNewerDirty (p : Loc) (γs : GName) (mp : Loc) (req : GMap GoString w64)
    (dq0 : DFrac) :
    isKV (hG := hG) p γs ⊢ ownMap mp dq0 req -∗
      <<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (Val #(methods (go.GoType.PointerType store.kv.KV.ty) go!"AllNewerDirty" #p))
          (Val #mp)) @ ∅
      <<{ storeOwn γs q S | (sl : GoSlice), RET (PairV #sl #interface.nil);
          ownMap mp dq0 req ∗ itemsIn sl S (fun _ _ _ c => c = false) }>> := by
  iintro #Hkv Hreq
  unfold isKV
  icases Hkv with ⟨%mpi, #Hitems, #Hmu, #Hpkg⟩
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
  iintro %kp ⟨Hkept, Hkcap⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoSlice) (fun _ (_ : Int) => iprop(
      ∃ (ns : GoSlice) (acc : List (Loc × (GoString × w64 × GoString × Bool))) (vi : GoSlice)
        (vk : GoString),
        newer_ptr ↦ ns ∗ ns ↦* acc.map Prod.fst ∗ ownSliceCap Loc ns (DFrac.own 1) ∗
        items_ptr ↦ vi ∗ key_ptr ↦ vk ∗ keyVersions_ptr ↦ mp ∗ ownMap mp dq0 req ∗
        ([∗map] k ↦ sl ∈ m, keyInv S0 k sl) ∗
        ([∗list] e ∈ acc, itemPtr e.1 e.2.1 e.2.2.1 e.2.2.2.1) ∗
        ⌜∀ e ∈ acc, (e.2.2.1, e.2.2.2.1, e.2.2.2.2) ∈ S0.items e.2.1 ∧ e.2.2.2.2 = false⌝))) $$ Hm
  iintro %keys %hkeys
  isplitl [newer Hkept Hkcap items key keyVersions Hreq Hmap]
  · iexists _, [], _, _
    simp only [List.map_nil]
    iframe
    isplitl []
    · iapply BigSepL.bigSepL_nil_intro (P := iprop(True)); itrivial
    · ipureintro; intro e he; cases he
  isplitl []
  · imodintro
    iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%ns, %acc, %vi, %vk, Hns, Hnsl, Hncap, Hitm, Hkey, HkV, Hreq,
      Hmap, Hacc, %Hacc⟩
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun k sl => keyInv (hG := hG) S0 k sl)
      (show get? m key = some v from hk2)).1 $$ Hmap with ⟨Hk, Hmap⟩
    unfold keyInv keyOwn
    icases Hk with ⟨%l, ⟨Hsl, Hcap, Hits⟩, %Hl⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    simp only [List.length_map] at Hlen
    wp_auto
    have hlpos : 0 < l.length := by
      cases l with
      | nil => exact absurd rfl Hl.1
      | cons _ _ => simp
    have Hb : 0 ≤ sint.Z (v.len - W64 1) ∧ sint.Z (v.len - W64 1) < sint.Z v.len := by
      constructor <;> word
    simp only [Hb.1, Hb.2, _root_.and_self, ↓reduceIte]
    have hidx : sint.nat (v.len - W64 1) = l.length - 1 := by word
    list_elem l (l.length - 1) as e
    icases ownSlice_elem_acc (sint.Z (v.len - W64 1)) e.1 v _ _ Hb.1
      (by rw [show (sint.Z (v.len - W64 1)).toNat = l.length - 1 by word, List.getElem?_map,
            He_lookup]; rfl) $$ Hsl with ⟨He1, Hsl⟩
    wp_auto
    ihave Hsl := Hsl $$ He1
    icases (BigSepL.bigSepL_lookup_acc He_lookup).1 $$ Hits with ⟨He, Hits⟩
    iunfold itemOwn at He
    iunfold itemPtr at He
    icases He with ⟨%Hnn, ⟨#HK, #HV, %vsl, #HVal, #Hx⟩, HC⟩
    wp_apply wp_map_lookup2 $$ Hreq as Hreq
    have hsetm : (List.map Prod.fst l).set (sint.Z (v.len - W64 1)).toNat e.fst = l.map Prod.fst := by
      apply list_set_lookup_self
      rw [show (sint.Z (v.len - W64 1)).toNat = l.length - 1 by word, List.getElem?_map, He_lookup]
      rfl
    rw [hsetm]
    have hmem : e ∈ l := List.mem_of_getElem? He_lookup
    have hin : (e.2.1, e.2.2.1, e.2.2.2) ∈ S0.items key := by
      rw [Hl.2]; exact List.mem_map_of_mem hmem
    ihave Hits := Hits $$ %e [HC]
    · unfold itemOwn itemPtr
      iframe HC HK HV
      isplitr
      · ipureintro; exact Hnn
      iexists vsl
      iframe #
    rw [list_set_lookup_self l _ e He_lookup]
    ihave Hmap := Hmap $$ [Hsl Hcap Hits]
    · iexists l
      iframe
      ipureintro; exact Hl
    cases hc : e.2.2.2
    · wp_auto
      cases hr : req !! key with
      | none =>
        wp_auto
        wp_apply wp_slice_literal (l := [e.1])
        isplitr
        · ipureintro; rfl
        iintro %kp1 ⟨Htmp, -⟩
        wp_auto
        wp_apply wp_slice_append (V := Loc) $$ [$Hnsl $Hncap $Htmp] as %ns' ⟨Hnsl, Hncap, -⟩
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists ns', acc ++ [(e.1, (key, e.2.1, e.2.2.1, false))], v, key
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe Hns Hnsl Hncap Hitm Hkey HkV Hreq Hmap
        isplitl [Hacc]
        · iapply BigSepL.bigSepL_snoc.2
          iframe Hacc
          unfold itemPtr
          iframe #
        · ipureintro
          intro e' he'
          rcases List.mem_append.1 he' with h | h
          · exact Hacc e' h
          · simp only [List.mem_singleton] at h; subst h
            exact ⟨by rw [← hc]; exact hin, rfl⟩
      | some h =>
        simp only [Option.isSome_some, Option.getD_some]
        wp_auto
        by_cases hlt : uint.Z h < uint.Z e.2.1
        · rw [decide_eq_true hlt]
          wp_auto
          wp_apply wp_slice_literal (l := [e.1])
          isplitr
          · ipureintro; rfl
          iintro %kp1 ⟨Htmp, -⟩
          wp_auto
          wp_apply wp_slice_append (V := Loc) $$ [$Hnsl $Hncap $Htmp] as %ns' ⟨Hnsl, Hncap, -⟩
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists ns', acc ++ [(e.1, (key, e.2.1, e.2.2.1, false))], v, key
          simp only [List.map_append, List.map_cons, List.map_nil]
          iframe Hns Hnsl Hncap Hitm Hkey HkV Hreq Hmap
          isplitl [Hacc]
          · iapply BigSepL.bigSepL_snoc.2
            iframe Hacc
            unfold itemPtr
            iframe #
          · ipureintro
            intro e' he'
            rcases List.mem_append.1 he' with h | h
            · exact Hacc e' h
            · simp only [List.mem_singleton] at h; subst h
              exact ⟨by rw [← hc]; exact hin, rfl⟩
        · rw [decide_eq_false hlt]
          wp_auto
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists ns, acc, v, key
          iframe
          ipureintro; exact Hacc
    · wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists ns, acc, v, key
      iframe
      ipureintro; exact Hacc
  iintro ⟨%ns, %acc, %vi, %vk, Hns, Hnsl, Hncap, Hitm, Hkey, HkV, Hreq, Hmap, Hacc, %Hacc⟩ Hm
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
  iframe Hreq
  unfold itemsIn
  iexists acc.map Prod.fst, acc.map Prod.snd
  iframe Hnsl
  isplitr
  · ipureintro
    refine ⟨by simp, ?_⟩
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
    exact Hacc a ha
  iapply acc_idx $$ Hacc

end proofs

end kvp

end github_com.despreston.go_craq

end Perennial
