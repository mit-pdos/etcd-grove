/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/Members.lean` (the clusterN
Scope, 2026-11-15). Lean-first (no Rocq counterpart).

The loop over `i` keeps `ms` the slice of `k` members whose first `i` are `membersOf`'s and the
rest zero; each iteration stores `memberAt i`, its three strings from `strconv.FormatUint`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Members
public import Spec.strconv.FormatUint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

theorem Members.wp_proof (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    Members.spec (GF := GF) (hG := hG) := by
  intro pfx k pb cb hk
  wp_start
  ihave #Pstr : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := GMember) k) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  (try wp_auto)
  have hk' : uint.Z k < 2 ^ 64 := by word
  ihave HI : (∃ (j : w64),
      "i" ∷ i_ptr ↦ j ∗
      "Hsl" ∷ sl ↦* (membersOf pfx (uint.nat j) pb cb ++
        List.replicate (uint.nat k - uint.nat j) (zero_val GMember)) ∗
      "%Hj" ∷ ⌜uint.Z j ≤ uint.Z k⌝ : IProp GF) $$ [i Hsl]
  · iexists W64 0
    iframe
    isplitl
    · iExactEq Hsl
      have hsk : sint.Z k = uint.Z k := by word
      have h00 : uint.nat (W64 0) = 0 := rfl
      rw [h00]
      simp only [sint.nat, hsk, membersOf, List.range_zero, List.map_nil, List.nil_append,
        Nat.sub_zero]
      rfl
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · wp_apply wp_FormatUint as %_ %Hs1
    · iframe #; ipureintro; decide
    wp_apply wp_FormatUint as %_ %Hs2
    · iframe #; ipureintro; decide
    wp_apply wp_FormatUint as %_ %Hs3
    · iframe #; ipureintro; decide
    (try wp_auto)
    ihave %Hlen := ownSlice_len $$ Hsl
    simp only [List.length_append, membersOf_length, List.length_replicate] at Hlen
    have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by
      obtain ⟨h1, h2⟩ := Hlen
      constructor <;> word
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index sl (sint.Z j) _ _) $$ [Hsl] as Hsl
    · iframe Hsl
      ipureintro
      simp only [List.length_append, membersOf_length, List.length_replicate]
      constructor <;> word
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    isplitl
    · iExactEq Hsl
      subst Hs1 Hs2 Hs3
      have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
      have hjz : (sint.Z j).toNat = uint.nat j := by word
      have hjw : (W64 ((uint.nat j : Nat) : Int)) = j := by word
      rw [hj1, hjz, ← membersOf_set pfx pb cb (uint.nat j) (uint.nat k) (by word), hjw]
      rfl
    ipureintro; word
  · (try wp_auto)
    iapply HΦ
    iExactEq Hsl
    have hjk : j = k := by word
    subst hjk
    simp

end proof

end etcdstart
end EtcdGrove
end Perennial
