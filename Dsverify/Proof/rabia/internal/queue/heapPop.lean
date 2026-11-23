/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/queue/heapPop.lean`, run `rabia-r1wake-1`.)

The proof of `container/heap.Pop(&q)` for a `PQueue` (`heapPop.spec`): `Swap(0, n-1)`,
`down(h, 0, n-1)` (a permutation, `wp_heap_down`), then `q.Pop()` removes the last element.
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

theorem heapPop.wp_proof
    (wp_Len : PQueue.Len.spec (GF := GF) (hG := hG))
    (wp_lt : ProxySeqIdLessThan.spec (GF := GF) (hG := hG)) :
    heapPop.spec (GF := GF) (hG := hG) := fun q xs hne => by
  wp_start as H
  ihave #Hsrt := pq_isSorter wp_Len wp_lt q $$ Hpkg
  icases pqOwn_len q xs $$ H with ⟨H, %Hl⟩
  wp_auto
  wp_apply wp_Len q xs slice.nil $$ [$Hpkg $H] as H
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hn : sint.nat (W64 xs.length - W64 1) = xs.length - 1 := by word
  have h0 : sint.nat (W64 0) = 0 := rfl
  list_elem xs 0 as x0
  list_elem xs (xs.length - 1) as xl
  wp_apply wp_pq_Swap q xs (W64 0) (W64 xs.length - W64 1) x0 xl (by word) (by word)
    (by rw [h0]; exact Hx0_lookup) (by rw [hn]; exact Hxl_lookup) $$ H as H
  simp only [pqIface_eq]
  have hp1 := slices.swap_perm xs (xs.length - 1) 0 xl x0 Hxl_lookup Hx0_lookup
  rw [hn]
  have hl1 : ((xs.set 0 xl).set (xs.length - 1) x0).length = xs.length := by simp
  wp_apply wp_heap_down (pqx q) (pqOwn q) objLt _ (W64 0) (W64 xs.length - W64 1)
    (by word) (by rw [hl1]; word) (by word) (by rw [hl1]; word) $$ [$Hsrt $H]
    as %b ⟨%xs2, H, %Hp2⟩
  have hne2 : xs2 ≠ [] := by
    intro h; subst h
    have := Hp2.length_eq; simp at this; omega
  wp_apply wp_pq_Pop q xs2 hne2 $$ H as %v ⟨%o, %Hsplit, #Ho, H⟩
  iapply HΦ
  iexists o, xs2.dropLast
  iframe Ho H
  ipureintro
  have e1 : (o :: xs2.dropLast) ≡ₚ xs2 := by
    have := (List.perm_append_comm (l₁ := [o]) (l₂ := xs2.dropLast))
    rw [Hsplit] at this; exact this
  exact e1.trans (Hp2.trans hp1.symm)

end proof

end Perennial.rabia.internal.queue
