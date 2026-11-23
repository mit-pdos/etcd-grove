/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/queue/HeapBasics.lean`, run `rabia-r1wake-1`.)

`container/heap`'s unexported `down` and `up` over a `heap.Interface` value meeting
`sort`'s sorter specs (`isSorter`: `Len`, `Less`, `Swap`): each permutes the elements (the heap
order, which the specs of this package do not need, is not proved). Lemmas: `heap`'s Go code
has no specs of its own in this project.
-/
module

public import Dsverify.Proof.rabia.internal.queue.Basics

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.queue

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode sort

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [container.heap.Assumptions]

theorem wp_heap_down {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    (xs : List E) (i0 n : w64) (hi0 : 0 ≤ sint.Z i0) (hi0l : sint.Z i0 < xs.length)
    (hn : 0 ≤ sint.Z n) (hnl : sint.Z n ≤ xs.length) :
    {{ isSorter x own R ∗ own xs }}
      (App (App (App (Val (@! container.heap.down)) (Val #(interface.ok x))) (Val #i0)) (Val #n))
    {{ (b : Bool), RET #b; ∃ xs', own xs' ∗ ⌜xs' ≡ₚ xs⌝ }} := by
  wp_start as ⟨#Hsrt, Hxs⟩
  wp_auto
  ihave HI : (∃ (iv : w64) (xs' : List E),
      "i" ∷ i_ptr ↦ iv ∗ "Hxs" ∷ own xs' ∗
      "%Hperm" ∷ ⌜xs' ≡ₚ xs⌝ ∗
      "%Hb" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv < xs.length⌝ : IProp GF) $$ [i Hxs]
  · iexists i0, xs
    iframe
    ipureintro
    exact ⟨List.Perm.refl _, hi0, hi0l⟩
  wp_for HI
  have hlen := Hperm.length_eq
  wp_if_destruct
  · wp_for_post
    iapply HΦ
    iexists xs'
    iframe Hxs
    ipureintro; exact Hperm
  wp_if_destruct
  · wp_for_post
    iapply HΦ
    iexists xs'
    iframe Hxs
    ipureintro; exact Hperm
  have hj1 : sint.Z (W64 2 * iv + W64 1) = 2 * sint.Z iv + 1 := by word
  wp_join iprop(∃ (jv : w64), "j" ∷ j_ptr ↦ jv ∗ "Hxs" ∷ own xs' ∗
      "h" ∷ h_ptr ↦ (interface.ok x : GoInterface) ∗
      "%Hjv" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv < sint.Z n⌝)
    with [j Hxs j1 j2 h] as ⟨%jv, j, Hxs, h, %Hjv⟩
  · -- `j2 < n`: compare the children
    have hj2 : sint.Z (W64 2 * iv + W64 1 + W64 1) = 2 * sint.Z iv + 2 := by word
    have hl2 : sint.nat (W64 2 * iv + W64 1 + W64 1) < xs'.length := by word
    have hl1 : sint.nat (W64 2 * iv + W64 1) < xs'.length := by word
    list_elem xs' (sint.nat (W64 2 * iv + W64 1 + W64 1)) as e2
    list_elem xs' (sint.nat (W64 2 * iv + W64 1)) as e1
    wp_apply wp_sorter_Less x own R xs' _ _ e2 e1 (by word) (by word) He2_lookup He1_lookup
      $$ [$Hsrt $Hxs] as %r ⟨Hxs, -⟩
    cases r
    · (try bool_if)
      wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro; constructor <;> word
    · (try bool_if)
      wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro; constructor <;> word
  · iexists _
    iframe
    ipureintro; constructor <;> word
  have hlj : sint.nat jv < xs'.length := by word
  have hli : sint.nat iv < xs'.length := by word
  list_elem xs' (sint.nat jv) as ej
  list_elem xs' (sint.nat iv) as ei
  wp_apply wp_sorter_Less x own R xs' _ _ ej ei Hjv.1 Hb.1 Hej_lookup Hei_lookup
    $$ [$Hsrt $Hxs] as %r ⟨Hxs, -⟩
  cases r
  · -- not less: break
    (try bool_if)
    wp_auto
    wp_for_post
    iapply HΦ
    iexists xs'
    iframe Hxs
    ipureintro; exact Hperm
  · (try bool_if)
    wp_auto
    wp_apply wp_sorter_Swap x own R xs' _ _ ei ej Hb.1 Hjv.1 Hei_lookup Hej_lookup
      $$ [$Hsrt $Hxs] as Hxs
    wp_for_post
    iframe
    iexists jv, _
    iframe
    ipureintro
    refine ⟨?_, Hjv.1, by word⟩
    exact (slices.swap_perm xs' _ _ ei ej Hei_lookup Hej_lookup).symm.trans Hperm

theorem wp_heap_up {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    (xs : List E) (j0 : w64) (hj0 : 0 ≤ sint.Z j0) (hj0l : sint.Z j0 < xs.length) :
    {{ isSorter x own R ∗ own xs }}
      (App (App (Val (@! container.heap.up)) (Val #(interface.ok x))) (Val #j0))
    {{ RET #(); ∃ xs', own xs' ∗ ⌜xs' ≡ₚ xs⌝ }} := by
  wp_start as ⟨#Hsrt, Hxs⟩
  wp_auto
  ihave HI : (∃ (jv : w64) (xs' : List E),
      "j" ∷ j_ptr ↦ jv ∗ "Hxs" ∷ own xs' ∗
      "%Hperm" ∷ ⌜xs' ≡ₚ xs⌝ ∗
      "%Hb" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv < xs.length⌝ : IProp GF) $$ [j Hxs]
  · iexists j0, xs
    iframe
    ipureintro
    exact ⟨List.Perm.refl _, hj0, hj0l⟩
  wp_for HI
  have hlen := Hperm.length_eq
  wp_if_destruct
  · wp_for_post
    iapply HΦ
    iexists xs'
    iframe Hxs
    ipureintro; exact Hperm
  have hpb : 0 ≤ sint.Z (BitVec.sdiv (jv - W64 1) (W64 2)) ∧
      sint.Z (BitVec.sdiv (jv - W64 1) (W64 2)) < sint.Z jv := by word
  have hlj : sint.nat jv < xs'.length := by word
  have hli : sint.nat (BitVec.sdiv (jv - W64 1) (W64 2)) < xs'.length := by word
  list_elem xs' (sint.nat jv) as ej
  list_elem xs' (sint.nat (BitVec.sdiv (jv - W64 1) (W64 2))) as ei
  wp_apply wp_sorter_Less x own R xs' _ _ ej ei Hb.1 hpb.1 Hej_lookup Hei_lookup
    $$ [$Hsrt $Hxs] as %r ⟨Hxs, -⟩
  cases r
  · (try bool_if)
    wp_auto
    wp_for_post
    iapply HΦ
    iexists xs'
    iframe Hxs
    ipureintro; exact Hperm
  · (try bool_if)
    wp_auto
    wp_apply wp_sorter_Swap x own R xs' _ _ ei ej hpb.1 Hb.1 Hei_lookup Hej_lookup
      $$ [$Hsrt $Hxs] as Hxs
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨?_, hpb.1, by word⟩
    exact (slices.swap_perm xs' _ _ ei ej Hei_lookup Hej_lookup).symm.trans Hperm

end proof

end Perennial.rabia.internal.queue
