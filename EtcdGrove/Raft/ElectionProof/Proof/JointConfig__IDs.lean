/-
Port of `election_proof/proof_JointConfig__IDs.v`.

Lean notes: Perennial's Lean `wp_map_for_range` (`Golang/Theory/Map.lean`) does not
hand the map's points-to back after the loop, while the Rocq proof gets it back
(`iIntros "HP Hvoters"`) and re-seals the tracker with it. `wp_map_for_range_own`
below is a copy of the one in `Proof/MajorityConfig__Slice.lean` (proofs do not import
each other), which gives the map's points-to back at every exit. Rocq's
`Proof using Type` remark does not apply: the Lean theorem's binders are the section
variables the spec mentions.
-/
import EtcdGrove.Raft.ElectionProof.Spec.JointConfig__IDs

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

theorem quorum.JointConfig.IDs.wp_proof :
    quorum.JointConfig.IDs.spec (GF := GF) (hG := hG) := by
  intro cfg trk tv t
  obtain ⟨votes, prs, pvs⟩ := t
  wp_start as ⟨Htrk, Hown⟩
  iNamed Hown
  -- `wp_auto` reads `r.trk.Config.Voters` out of `trk ↦ tv` and reduces the pointer
  -- method to the value method applied to the `JointConfig` value.
  wp_auto
  dsimp only
  wp_method_call
  wp_call
  -- `GoAlloc JointConfig` gives `"c" ∷ c_ptr ↦ tv.Config'.Voters'`
  wp_auto
  -- `m := map[uint64]struct{}{}`
  wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
  -- `c[0]`: peel element 0 off the array; `Hvoters_arr` says it is `voters_ref`.
  icases array_acc _ (sint.Z (W64 0)) _ _ _ voters_ref (by decide) (by rw [Hvoters_arr]; rfl)
    $$ c with ⟨Hc0, Hcback⟩
  wp_auto
  -- `for id := range c[0] { m[id] = struct{}{} }`. The invariant carries the domain of
  -- the partial map: after `i` iterations it is the first `i` keys of the enumeration.
  -- `id` is the loop variable, assigned every iteration, so it is existentially
  -- quantified inside the invariant.
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_own (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
      (idm : GMap w64 Unit),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hidm" ∷ ⌜∀ k, k ∈ domSet idm ↔ k ∈ keys.take i.toNat⌝ ∗
      "id" ∷ id_ptr ↦ x ∗
      "m" ∷ m_ptr ↦ mref ∗
      "Hmref" ∷ mref ↦$ idm)) $$ Hvoters
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id m Hmref]
  · iexists zero_val w64, ∅
    simp only [named]
    iframe id m Hmref
    ipureintro
    refine ⟨Int.le_refl _, fun k => ?_⟩
    simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, iff_false]
    rw [GMap.elem_of_dom]
    rintro ⟨v, hv⟩
    simp at hv
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_mapInsert $$ Hmref as Hmref
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, _
    simp only [named]
    iframe id m Hmref
    ipureintro
    refine ⟨by omega, fun k => ?_⟩
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, List.mem_append, List.mem_singleton, ← Hidm, GMap.elem_of_dom,
      GMap.elem_of_dom]
    by_cases hk : key = k
    · subst hk; simp
    · rw [GMap.lookup_insert_ne _ _ hk]
      constructor
      · intro h; exact .inl h
      · rintro (h | h)
        · exact h
        · exact absurd h.symm hk
  -- the range is over: `domSet idm` is every key, i.e. `domSet voters = cfg`
  iintro HP Hvoters
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hidm
  -- `c[1]`: put element 0 back, peel element 1 off; it is `map.nil`, and ranging over
  -- the nil map is the pure step `wp_map_nil_for_range`, which `wp_auto` takes once the
  -- loop variable is allocated.
  ihave c := Hcback $$ Hc0
  icases array_acc _ (sint.Z (W64 1)) _ _ _ map.nil (by decide) (by rw [Hvoters_arr]; rfl)
    $$ c with ⟨Hc1, Hcback⟩
  wp_auto
  wp_func_lits
  wp_auto
  -- `return m`. `iframe Hmref` before the split could be matched against `ownTracker`'s
  -- own `voters_ref ↦$ voters`; re-seal the tracker first.
  iapply HΦ
  iframe Htrk
  isplitl [Hvotes Hprogs Hvoters Hlearners HlearnersNext]
  · iapply ownTracker_intro cfg tv votes prs pvs voters_ref voters learners learnersNext
      Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
      $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext
  iframe Hmref
  ipureintro
  rw [← Hvoters_dom]
  apply GMap.set_eq; intro k
  rw [Hidm, Hkset, GMap.elem_of_dom, Option.isSome_iff_exists]

end proof

end EtcdGrove
end Perennial
