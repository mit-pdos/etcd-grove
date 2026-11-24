/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/queue/heapPush.lean`, run `rabia-r1wake-1`.)

The proof of `container/heap.Push(&q, x)` for a `PQueue` (`heapPush.spec`): `q.Push(x)` appends,
then `up(h, n-1)` permutes (`wp_heap_up`).
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

theorem heapPush.wp_proof
    (wp_Len : PQueue.Len.spec (GF := GF) (hG := hG))
    (wp_lt : ProxySeqIdLessThan.spec (GF := GF) (hG := hG)) :
    heapPush.spec (GF := GF) (hG := hG) := fun q xs v o => by
  wp_start as ⟨H, #Ho⟩
  ihave #Hsrt := pq_isSorter wp_Len wp_lt q $$ Hpkg
  wp_auto
  wp_apply wp_pq_Push q xs v o $$ [$H $Ho] as H
  icases pqOwn_len q _ $$ H with ⟨H, %Hl⟩
  wp_apply wp_Len q (xs ++ [o]) slice.nil $$ [$Hpkg $H] as H
  simp only [pqIface_eq]
  have hl : (xs ++ [o]).length = xs.length + 1 := by simp
  rw [hl] at Hl ⊢
  wp_apply wp_heap_up (pqx q) (pqOwn q) objLt _ (W64 (xs.length + 1 : Nat) - W64 1)
    (by word) (by rw [hl]; word) $$ [$Hsrt $H] as ⟨%xs2, H, %Hp2⟩
  iapply HΦ
  iexists xs2
  iframe H
  ipureintro
  exact Hp2.trans (List.perm_append_singleton o xs)

end proof

end Perennial.rabia.internal.queue
