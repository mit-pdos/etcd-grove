/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/RandomOptions.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.RandomOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem RandomOptions.wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG)) :
    RandomOptions.spec (GF := GF) (hG := hG) := by
  wp_start as #Hpkg
  try wp_auto
  wp_apply wp_below as %v %Hv
  wp_apply wp_oneIn (W64 2) (by decide) as %b1 -
  wp_apply wp_oneIn (W64 2) (by decide) as %b2 -
  wp_apply wp_oneIn (W64 2) (by decide) as %b3 -
  wp_apply wp_slice_literal (l := [W64 0, W64 256, W64 4096, W64 1048576])
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨Hs1, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (4 : Int) 0) 0 = 4 from rfl]
  wp_apply wp_below as %r1 %Hr1
  have h1 : 0 ≤ sint.Z r1 ∧ sint.Z r1 < sint.Z (W64 4) := by
    have := Hr1.2 (by decide); constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  list_elem [W64 0, W64 256, W64 4096, W64 1048576] (sint.Z r1).toNat as x1
  wp_apply wp_load_slice_index _ (sint.Z r1) _ _ x1 h1.1 $$ [Hs1] with -
  · iframe; ipureintro; exact Hx1_lookup
  wp_apply wp_slice_literal (l := [W64 1, W64 4, W64 256])
  isplitr
  · ipureintro; rfl
  iintro %s2 ⟨Hs2, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (3 : Int) 0) 0 = 3 from rfl]
  wp_apply wp_below as %r2 %Hr2
  have h2 : 0 ≤ sint.Z r2 ∧ sint.Z r2 < sint.Z (W64 3) := by
    have := Hr2.2 (by decide); constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
  list_elem [W64 1, W64 4, W64 256] (sint.Z r2).toNat as x2
  wp_apply wp_load_slice_index _ (sint.Z r2) _ _ x2 h2.1 $$ [Hs2] with -
  · iframe; ipureintro; exact Hx2_lookup
  have hx2 : x2 ∈ [W64 1, W64 4, W64 256] := List.mem_of_getElem? Hx2_lookup
  wp_apply wp_slice_literal (l := [W64 0, W64 4096, W64 1048576])
  isplitr
  · ipureintro; rfl
  iintro %s3 ⟨Hs3, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (3 : Int) 0) 0 = 3 from rfl]
  wp_apply wp_below as %r3 %Hr3
  have h3 : 0 ≤ sint.Z r3 ∧ sint.Z r3 < sint.Z (W64 3) := by
    have := Hr3.2 (by decide); constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
  list_elem [W64 0, W64 4096, W64 1048576] (sint.Z r3).toNat as x3
  wp_apply wp_load_slice_index _ (sint.Z r3) _ _ x3 h3.1 $$ [Hs3] with -
  · iframe; ipureintro; exact Hx3_lookup
  try wp_auto
  have hv : 1 ≤ uint.Z (W64 1 + v) ∧ uint.Z (W64 1 + v) ≤ 5 := by
    have := Hv.2 (by decide); constructor <;> word
  have hi : 0 < sint.Z x2 ∧ sint.Z x2 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2
    rcases hx2 with rfl | rfl | rfl <;> decide
  wp_if_destruct
  · -- `MaxSizePerMsg == 0`
    try wp_auto
    wp_if_destruct
    · try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨hv.1, hv.2, hi.1, hi.2, Or.inl (show W64 4096 ≠ W64 0 by decide)⟩
    · try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨hv.1, hv.2, hi.1, hi.2, Or.inl Hif⟩
  · try wp_auto
    iapply HΦ
    ipureintro
    exact ⟨hv.1, hv.2, hi.1, hi.2, Or.inr Hif⟩

end proof

end kvreconf
end EtcdGrove
end Perennial
