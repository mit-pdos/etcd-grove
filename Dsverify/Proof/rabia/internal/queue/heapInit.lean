/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/queue/heapInit.lean`, run `rabia-r1wake-1`.)

The proof of `container/heap.Init(&q)` for a `PQueue` (`heapInit.spec`): `down(h, i, n)` for
`i` from `n/2 - 1` down to `0`, each a permutation (`wp_heap_down`).
-/
module

public import Dsverify.Proof.rabia.internal.queue.Methods
public import Dsverify.Proof.rabia.internal.queue.HeapBasics

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.queue

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.queue.Assumptions]
variable [container.heap.Assumptions]

theorem heapInit.wp_proof
    (wp_Len : PQueue.Len.spec (GF := GF) (hG := hG))
    (wp_lt : ProxySeqIdLessThan.spec (GF := GF) (hG := hG)) :
    heapInit.spec (GF := GF) (hG := hG) := fun q xs => by
  wp_start as H
  ihave #Hsrt := pq_isSorter wp_Len wp_lt q $$ Hpkg
  icases pqOwn_len q _ $$ H with ⟨H, %Hl⟩
  wp_auto
  wp_apply wp_Len q xs slice.nil $$ [$Hpkg $H] as H
  simp only [pqIface_eq]
  ihave HI : (∃ (iv : w64) (xs' : List ObjV),
      "i" ∷ i_ptr ↦ iv ∗ "H" ∷ pqOwn q xs' ∗
      "%Hperm" ∷ ⌜xs' ≡ₚ xs⌝ ∗
      "%Hb" ∷ ⌜-1 ≤ sint.Z iv ∧ sint.Z iv < xs.length⌝ : IProp GF) $$ [i H]
  · iexists _, xs
    iframe
    ipureintro
    exact ⟨List.Perm.refl _, by word, by word⟩
  wp_for HI
  have hlen := Hperm.length_eq
  wp_if_destruct
  · wp_apply wp_heap_down (pqx q) (pqOwn q) objLt xs' iv (W64 xs.length)
      (by word) (by rw [hlen]; word) (by word) (by rw [hlen]; word) $$ [$Hsrt $H]
      as %b ⟨%xs2, H, %Hp2⟩
    wp_for_post
    iframe
    iexists _, xs2
    iframe
    ipureintro
    exact ⟨Hp2.trans Hperm, by word, by word⟩
  · iapply HΦ
    iexists xs'
    iframe H
    ipureintro; exact Hperm

end proof

end Perennial.rabia.internal.queue
