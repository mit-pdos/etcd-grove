/- Port of election_proof/proof_MajorityConfig__Slice.v.

Lean notes: Perennial's Lean `wp_map_for_range` (`Golang/Theory/Map.lean`) does not
hand the map's points-to back after the loop (its final continuation is
`P keys (size m) -∗ Φ executeVal`), while the Rocq proof gets it back (`iIntros "HP
Hm"`) and the postcondition needs it (`ownIdsetOpt m ids`). `wp_map_for_range_own`
below is a copy of that proof that re-seals the map from the `FinishRead`'s points-to
and passes it to the continuation (and to a `break`/`return` exit). -/
import EtcdGrove.Raft.ElectionProof.Spec.MajorityConfig__Slice
import EtcdGrove.Raft.ElectionProof.Spec.slices_Sort

noncomputable section

namespace Perennial

section forRange
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

/-- `wp_map_for_range`, giving the map's points-to back at every exit. -/
private theorem wp_map_for_range_own (P : List K → Int → IProp GF) (body : GoFunc)
    (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V) (dq : DFrac)
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K key_type] (Φ : val → IProp GF) :
    (mref ↦${dq} m : IProp GF) -∗
    (∀ keys : List K,
      ⌜(∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = GMap.size m ∧ keys.Nodup⌝ -∗
      (P keys 0 ∗
       □ (∀ (i : Int) (key : K) (v : V), ⌜keys[i.toNat]? = some key ∧ m !! key = some v⌝ -∗
          P keys i -∗
          WP (App (App (Val #body) (Val #key)) (Val #v)) @ s; E
            {{ v, forMapPostcondition (P keys (i + 1)) (fun v => iprop(mref ↦${dq} m -∗ Φ v)) v }}) ∗
       (P keys (GMap.size m) -∗ mref ↦${dq} m -∗ Φ executeVal))) -∗
    WP (App (App (Val (map.forRange key_type elem_type)) (Val #mref)) (Val #body)) @ s; E {{ Φ }} := by
  iintro Hm HΦ
  ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
  wp_call
  rw [decide_eq_false Hnn]
  wp_pures
  rw [ownMap_unseal]
  iNamed Hm
  have Hreseal : ⊢ heapPointsto (GF := GF) mref dq mv -∗ ownMapDef (V := V) mref dq m := by
    iintro Hown
    unfold ownMapDef
    iexists mv, mp
    simp only [named]
    iframe Hown
    ipureintro
    exact ⟨His_map, Hagree, Hdom, Hdefault⟩
  wp_apply wp_start_read $$ Hown with ⟨Hown, Hclose⟩
  wp_bind (App (Val (GoInstruction (InternalMapForRange key_type elem_type))) _)
  iapply wp_InternalMapForRange mv mp #body key_type elem_type _ $$ %His_map
  iintro %e' %He'
  rw [go.internal_map_domain_literal_step_pure mv mp #body key_type elem_type His_map] at He'
  obtain ⟨ks, hks, rfl⟩ := He'
  obtain ⟨Hnodup, Hks⟩ := go.is_map_domain_pure mv mp ks His_map hks
  obtain ⟨keys, rfl⟩ := list_exists_map_of_forall (intoVal (V := K)) ks
    (fun kv hkv => Hdom kv ((Hks kv).2 hkv))
  have Hmem : ∀ k, k ∈ keys ↔ (m !! k).isSome := by
    intro k
    rw [← list_mem_map_inj (intoVal (V := K)) go.intoVal_inj, ← Hks, Hagree k]
    cases m !! k <;> simp
  have Hnd : keys.Nodup := list_nodup_of_map _ _ Hnodup
  have Hsize : keys.length = GMap.size m := (GMap.size_eq_length m keys Hnd Hmem).symm
  icases HΦ $$ %keys %(⟨Hmem, Hsize, Hnd⟩) with ⟨HP, #Hiter, HΦ⟩
  obtain ⟨i, hi⟩ : ∃ i : Nat, i = 0 := ⟨0, rfl⟩
  have hile : i ≤ keys.length := by omega
  rw [show List.map intoVal keys = List.map intoVal (keys.drop i) by rw [hi, List.drop_zero],
    show P keys 0 = P keys (i : Int) by rw [hi]; rfl]
  clear hi
  iloeb as IH generalizing %i %hile
  by_cases hlt : i < keys.length
  · have hkey : keys[i]? = some keys[i] := List.getElem?_eq_getElem hlt
    obtain ⟨v, hv⟩ : ∃ v, m !! keys[i] = some v :=
      Option.isSome_iff_exists.1 ((Hmem _).1 (List.getElem_mem hlt))
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.foldr_cons]
    simp only [Hagree keys[i], hv]
    ihave Hb := Hiter $$ %(i : Int) %(keys[i]) %v %(⟨by simp only [Int.toNat_natCast]; exact hkey, hv⟩) HP
    wp_bind (App (App (Val #body) (Val #(keys[i]))) (Val #v))
    iapply wp_wand $$ Hb
    iintro %bv Hpost
    unfold forMapPostcondition
    have hcast : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by push_cast; rfl
    icases Hpost with (⟨%hbv, HP⟩ | ⟨%hbv, HP⟩ | ⟨%hbv, HΦ'⟩ | ⟨%v', %hbv, HΦ'⟩)
    · subst hbv
      rw [continueVal_unseal]; simp only [continueValDef]
      wp_auto
      rw [← hcast]
      iapply IH $$ %(i + 1) %(by omega) Hown Hclose HP HΦ
    · subst hbv
      rw [executeVal_unseal]; simp only [executeValDef]
      wp_auto
      rw [← hcast]
      iapply IH $$ %(i + 1) %(by omega) Hown Hclose HP HΦ
    · subst hbv
      rw [breakVal_unseal]; simp only [breakValDef]
      wp_auto
      wp_apply wp_finish_read $$ [Hown Hclose] with Hown
      · iframe Hown Hclose
      iapply HΦ'
      iapply Hreseal $$ Hown
    · subst hbv
      rw [returnVal_unseal]; simp only [returnValDef]
      wp_auto
      wp_apply wp_finish_read $$ [Hown Hclose] with Hown
      · iframe Hown Hclose
      iapply HΦ'
      iapply Hreseal $$ Hown
  · rw [List.drop_of_length_le (by omega)]
    simp only [List.map_nil, List.foldr_nil]
    wp_auto
    wp_apply wp_finish_read $$ [Hown Hclose] with Hown
    · iframe Hown Hclose
    have hsz : (i : Int) = (GMap.size m : Int) := by omega
    rw [hsz]
    iapply HΦ $$ HP
    iapply Hreseal $$ Hown

end forRange

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem quorum.MajorityConfig.Slice.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG)) :
    quorum.MajorityConfig.Slice.spec (GF := GF) (hG := hG) := by
  intro m ids
  wp_start as Hm
  wp_auto
  unfold ownIdsetOpt
  icases Hm with (%Hnil | Hm)
  · -- the nil set: the range is a pure step, and `sl` stays nil
    obtain ⟨rfl, rfl⟩ := Hnil
    wp_func_lits
    wp_auto
    ihave Hsl0 : (slice.nil ↦* ([] : List w64)) $$ []
    · iapply ownSlice_nil
    wp_apply wp_slices_Sort $$ [$Hsl0] as %xs ⟨Hsl, %Hxs, -⟩
    iapply HΦ
    iframe Hsl
    isplitl []
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro
    rw [GMap.dom_empty]
    have : (∅ : GSet w64).elements = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [this]
    exact Hxs.symm
  · wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range_own (fun (keys : List w64) (i : Int) => iprop(∃ (sl' : GoSlice) (x : w64),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "sl" ∷ sl_ptr ↦ sl' ∗
        "Hsl" ∷ sl' ↦* keys.take i.toNat ∗
        "Hsl_cap" ∷ ownSliceCap w64 sl' (DFrac.own 1) ∗
        "id" ∷ id_ptr ↦ x)) $$ Hm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [sl id]
    · iexists slice.nil, zero_val w64
      simp only [Int.toNat_zero, List.take_zero, named]
      iframe sl id
      isplitl []
      · ipureintro; omega
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      wp_apply wp_slice_literal (V := w64) [key]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hsl $Hsl_cap $Hsl2]
        as %sl3 ⟨Hsl, Hsl_cap, -⟩
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega]
        rw [List.take_add_one, Hkey]; rfl
      iexists sl3, key
      rw [Htake]
      simp only [named]
      iframe sl Hsl Hsl_cap id
      ipureintro; omega
    iintro HP Hm
    iNamed HP
    rw [show (GMap.size ids : Int).toNat = keys.length by omega, List.take_length]
    wp_auto
    wp_apply wp_slices_Sort $$ [$Hsl] as %xs ⟨Hsl, %Hxs, -⟩
    iapply HΦ
    iframe Hsl Hsl_cap
    isplitl [Hm]
    · iright; iexact Hm
    ipureintro
    refine Hxs.symm.trans ((List.perm_ext_iff_of_nodup Hknodup (GMap.NoDup_elements _)).2 ?_)
    intro k
    rw [GMap.elem_of_elements, GMap.elem_of_dom, Hkset, Option.isSome_iff_exists]

end proof

end EtcdGrove
end Perennial
