/-
Port of `election_proof/proof_JointConfig__IDs.v`.

Lean notes: Perennial's `wp_map_for_range` hands the map's points-to back after the
loop, as Rocq's (`iIntros "HP Hvoters"`), and the tracker is re-sealed with it. Rocq's
`Proof using Type` remark does not apply: the Lean theorem's binders are the section
variables the spec mentions.
-/
import EtcdGrove.Raft.Spec.JointConfig__IDs

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

theorem quorum.JointConfig.IDs.wp_proof :
    quorum.JointConfig.IDs.spec (GF := GF) (hG := hG) := by
  intro p jc v vm dq dqv Harr
  wp_start as ⟨Hp, Hvoters⟩
  -- `wp_auto` reads the `JointConfig` out of `p ↦{dq} jc` and reduces the pointer method
  -- to the value method applied to the `JointConfig` value.
  wp_auto
  wp_method_call
  wp_call
  -- `GoAlloc JointConfig` gives `"c" ∷ c_ptr ↦ jc`
  wp_auto
  -- `m := map[uint64]struct{}{}`
  wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
  -- `c[0]`: peel element 0 off the array; `Harr` says it is `v`.
  icases array_acc _ (sint.Z (W64 0)) _ _ _ v (by decide) (by rw [Harr]; rfl)
    $$ c with ⟨Hc0, Hcback⟩
  wp_auto
  -- `for id := range c[0] { m[id] = struct{}{} }`. The invariant carries the domain of
  -- the partial map: after `i` iterations it is the first `i` keys of the enumeration.
  -- `id` is the loop variable, assigned every iteration, so it is existentially
  -- quantified inside the invariant.
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
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
  -- the range is over: `domSet idm` is every key, i.e. `domSet vm`
  iintro HP Hvoters
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hidm
  -- `c[1]`: put element 0 back, peel element 1 off; it is `map.nil`, and ranging over
  -- the nil map is the pure step `wp_map_nil_for_range`, which `wp_auto` takes once the
  -- loop variable is allocated.
  ihave c := Hcback $$ Hc0
  icases array_acc _ (sint.Z (W64 1)) _ _ _ map.nil (by decide)
    (by
      rw [list_set_lookup_self _ _ _ (show jc.arr[(sint.Z (W64 0)).toNat]? = some v by
        rw [Harr]; rfl)]
      show jc.arr[(sint.Z (W64 1)).toNat]? = some map.nil
      rw [Harr]; rfl)
    $$ c with ⟨Hc1, Hcback⟩
  wp_auto
  wp_func_lits
  wp_auto
  -- `return m`
  iapply HΦ
  iframe Hp Hvoters Hmref
  ipureintro
  apply GMap.set_eq; intro k
  rw [Hidm, Hkset, GMap.elem_of_dom, Option.isSome_iff_exists]

end proof

end EtcdGrove
end Perennial
