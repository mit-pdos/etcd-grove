/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/idNames.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.idNames
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

attribute [-instance] pure_wp_slice_for_range

/-- **A range loop over a slice the loop only reads** (a copy of
`Proof/go_etcd_io/raft/v3/DescribeConfChange.lean`'s `wp_slice_for_range_ro`, private there). -/
private theorem wp_slice_for_range_ro {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  unfold slice.forRange
  wp_auto
  ihave Hinv : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 j ∗ "HP" ∷ P j ∗ "Hs" ∷ sl ↦*{dq} vs ∗
      "HΦ" ∷ (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) ∗ "%Hj" ∷ ⌜j ≤ vs.length⌝ :
      IProp GF) $$ [i HP Hs HΦ]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for Hinv
  by_cases hj : j < vs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv ⟨%hbv, HP, Hs⟩
    subst hbv
    iapply wp_for_post_do
    wp_auto
    iframe
    iexists (j + 1)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    have hj1 : j + 1 ≤ vs.length := hj
    iframe
    ipureintro; exact hj1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = vs.length := by omega
    subst hjl
    iapply HΦ $$ HP Hs

theorem idNames.wp_proof (wp_Name : Name.spec (GF := GF) (hG := hG)) :
    idNames.spec (GF := GF) (hG := hG) := by
  intro sl dq ids
  wp_start as Hsl
  ihave %Hl := ownSlice_len $$ Hsl
  wp_auto
  wp_apply wp_slice_make3 (V := GoString) (W64 0) sl.len ⟨by decide, Hl.2⟩ as %o0 ⟨Ho, Hcap, -⟩
  try wp_auto
  wp_apply (wp_slice_for_range_ro (V := w64) _ sl ids dq _
    (fun i => iprop(∃ (o : GoSlice) (v : w64), out_ptr ↦ o ∗ o ↦* (ids.take i).map AntSim.nameOf ∗
      ownSliceCap GoString o (DFrac.own 1) ∗ id_ptr ↦ v))) $$ Hsl [out Ho Hcap id]
  · iexists o0, _
    iframe
  · imodintro
    iintro %i %x %hx ⟨%o, %v, out, Ho, Hcap, id⟩ Hsl
    try wp_auto
    wp_apply wp_Name x $$ [$Hpkg]
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append o _ _ [AntSim.nameOf x] (DFrac.own 1) $$ [$Ho $Hcap $Hsl1]
      as %o' ⟨Ho, Hcap, -⟩
    try wp_auto
    isplitr
    · ipureintro; rfl
    iframe
    rw [List.take_add_one, hx, Option.toList_some, List.map_append, List.map_singleton]
    iexact Ho
  iintro ⟨%o, %v, out, Ho, Hcap, id⟩ Hsl
  rw [List.take_length]
  imod ownSlice_persist $$ Ho with #Ho
  try wp_auto
  iapply HΦ
  iframe Hsl
  iunfold AntCheck.strsRO
  iexact Ho

end proof

end AntHarness
end EtcdGrove
end Perennial
