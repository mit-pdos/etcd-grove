/-
Proof of `Spec/Config__Clone.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Raft.Spec.Config__Clone

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem tracker.Config.Clone.wp_proof : tracker.Config.Clone.spec (GF := GF) (hG := hG) := by
  intro p cfg v vm dq dqv Hcfg
  obtain ⟨Harr, Hl, Hln⟩ := Hcfg
  wp_start as ⟨Hp, Hv⟩
  wp_alloc c_ptr as c; wp_pures; wp_alloc clone_ptr as clone; wp_pures; wp_store; wp_pures; wp_load
  wp_pures
  -- the receiver is read at fraction `dq`: split the struct into its fields, then peel
  -- `Voters[0]` and `Voters[1]` off the array
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  icases array_acc _ (sint.Z (W64 0)) _ _ _ v (by decide) (by rw [Harr]; rfl)
    $$ Voters with ⟨Hv0, Hvback⟩
  wp_load; wp_pures; wp_load; wp_pures; wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures
  -- `clone(c.Voters[0])`, inlined: the map is not nil, so it is copied key by key
  ihave %Hvnn := ownMap_not_nil _ _ _ $$ Hv
  wp_if_destruct
  · exact absurd rfl Hvnn
  wp_load; wp_pures
  wp_apply wp_map_len $$ Hv as Hv
  wp_pures
  wp_apply wp_map_make2 as %mref Hmref
  wp_pures; wp_alloc mm_ptr as mm; wp_pures; wp_store; wp_pures; wp_load; wp_pures
  wp_alloc k_ptr as k; wp_pures; iclear m
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
      (mv : GMap w64 Unit),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hmv" ∷ ⌜∀ k, k ∈ domSet mv ↔ k ∈ keys.take i.toNat⌝ ∗
      "k" ∷ k_ptr ↦ x ∗
      "mm" ∷ mm_ptr ↦ mref ∗
      "Hmref" ∷ mref ↦$ mv)) $$ Hv
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [k mm Hmref]
  · iexists zero_val w64, ∅
    simp only [named]
    iframe k mm Hmref
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
    wp_pures; wp_store; wp_pures; wp_load; wp_load
    wp_apply wp_mapInsert $$ Hmref as Hmref
    wp_pures
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, _
    simp only [named]
    iframe k mm Hmref
    ipureintro
    refine ⟨by omega, fun k => ?_⟩
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, List.mem_append, List.mem_singleton, ← Hmv, GMap.elem_of_dom,
      GMap.elem_of_dom]
    by_cases hk : key = k
    · subst hk; simp
    · rw [GMap.lookup_insert_ne _ _ hk]
      constructor
      · intro h; exact .inl h
      · rintro (h | h)
        · exact h
        · exact absurd h.symm hk
  iintro HP Hv
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
  -- the copy is `vm` itself: same keys, and the values are `()`
  have Hmv' : mv = vm := by
    apply GMap.map_eq; intro k
    have := Hmv k
    rw [Hkset, GMap.elem_of_dom] at this
    rcases h1 : mv !! k with _ | ⟨⟩ <;> rcases h2 : vm !! k with _ | ⟨⟩ <;> simp_all
  subst Hmv'
  -- `clone(c.Voters[1])`, `clone(c.Learners)`, `clone(c.LearnersNext)`: all `nil`, each
  -- call returns `nil` at once
  ihave Voters := Hvback $$ Hv0
  icases array_acc _ (sint.Z (W64 1)) _ _ _ map.nil (by decide)
    (by
      rw [list_set_lookup_self _ _ _ (show cfg.Voters'.arr[(sint.Z (W64 0)).toNat]? = some v by
        rw [Harr]; rfl)]
      show cfg.Voters'.arr[(sint.Z (W64 1)).toNat]? = some map.nil
      rw [Harr]; rfl)
    $$ Voters with ⟨Hv1, Hvback⟩
  wp_pures; wp_load; wp_pures
  wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures; iclear m
  rw [Hl, Hln]
  wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures; iclear m
  wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures; iclear m
  -- `return Config{...}`: the receiver back together, the fresh voter map `mref`
  iapply HΦ
  ihave Voters := Hvback $$ Hv1
  rw [list_set_lookup_self _ _ _ (show cfg.Voters'.arr[(sint.Z (W64 0)).toNat]? = some v by
    rw [Harr]; rfl)]
  rw [show (array.mk 2 cfg.Voters'.arr).arr = cfg.Voters'.arr from rfl]
  rw [list_set_lookup_self _ _ _ (show cfg.Voters'.arr[(sint.Z (W64 1)).toNat]? = some map.nil by
    rw [Harr]; rfl)]
  iframe Hv Hmref
  isplitl [AutoLeave Learners LearnersNext Voters]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    rw [Hl, Hln]
    iframe
  ipureintro
  exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

end proof

end EtcdGrove
end Perennial
