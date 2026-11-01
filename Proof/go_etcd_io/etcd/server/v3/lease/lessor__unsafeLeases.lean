/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__unsafeLeases.lean`. Lean-first (no Rocq
counterpart); the lease-read plan (2026-10-31).

The map's range appends each lease (the loop's invariant: the pairs so far, their ids the keys so
far, each a pair of the map), as `Set.UnsortedList`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__unsafeLeases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.unsafeLeases.wp_proof :
    lease.lessor.unsafeLeases.spec (GF := GF) (hG := hG) := by
  intro lp lm M q
  wp_start as ⟨Hlm, HM⟩
  (try wp_auto)
  wp_apply wp_map_len_lt $$ HM as ⟨HM, %Hsz⟩
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 (GMap.size M)) (by word)) as %sl0 ⟨Hsl0, Hcap0, -⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (p : Int) =>
      iprop(∃ (x : Loc) (sl : GoSlice) (cl : List (Loc × w64)),
      "%Hp" ∷ ⌜0 ≤ p ∧ cl.map Prod.snd = keys.take p.toNat ∧
        ∀ (id : w64) (l : Loc), (l, id) ∈ cl → M.lookup id = some l⌝ ∗
      "l" ∷ l_ptr ↦ x ∗ "leases" ∷ leases_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* cl.map Prod.fst ∗ "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1))) $$ HM
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [l leases Hsl0 Hcap0]
  · iexists _, sl0, []
    simp only [named, List.replicate_zero, List.map_nil]
    iframe
    ipureintro
    exact ⟨Int.le_refl _, by simp, fun _ _ h => by cases h⟩
  isplitr
  · imodintro
    iintro %p %k %o ⟨%Hkey, %Ho⟩ HP
    iNamed HP
    obtain ⟨Hp0, Hcl, Hin⟩ := Hp
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply wp_slice_append_dfrac $$ [$Hsl $Hcap $Hl1]
      as %sl' ⟨Hsl, Hcap, -⟩
    · ipureintro; exact DFrac.valid_own_one
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists o, sl', cl ++ [(o, k)]
    simp only [named, List.map_append, List.map_cons, List.map_nil]
    have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [k] := by
      rw [show (p + 1).toNat = p.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    iframe
    ipureintro
    refine ⟨by omega, by rw [Htake, Hcl], ?_⟩
    intro id l hm
    rcases List.mem_append.1 hm with hm | hm
    · exact Hin id l hm
    · rw [List.mem_singleton] at hm
      cases hm
      exact Ho
  · iintro HP HM
    iNamed HP
    obtain ⟨-, Hcl, Hin⟩ := Hp
    rw [← Hklen, Int.toNat_natCast, List.take_length] at Hcl
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    refine ⟨by rw [Hcl]; exact Hknodup, fun id l => ⟨Hin id l, fun h => ?_⟩⟩
    have hk : id ∈ cl.map Prod.snd := by
      rw [Hcl]; exact (Hkset id).2 (by rw [show M !! id = some l from h]; rfl)
    obtain ⟨⟨l', id'⟩, hm, rfl⟩ := List.mem_map.1 hk
    have := Hin _ _ hm
    rw [h] at this
    cases this
    exact hm

end proof

end EtcdGrove
end Perennial
