/-
The delaying queue's waiting heap as `container/heap`'s interface (`heap.heapIface`,
`heap.heapPopIface`), from `waitForPriorityQueue`'s methods' specs (hypotheses); the lessor's
queues' `queue_heapIface` (`Proof/go_etcd_io/etcd/server/v3/lease/QueueLemmas.lean`), adapted.
Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Len
public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Less
public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Swap
public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Push
public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Pop
public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Peek

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]
variable {K : Type} {T : go.GoType} [QItem (GF := GF) K T]

/-- **`pq` is a `heap.Interface`** over `wqHeap pq`. -/
theorem wq_heapIface
    (hLen : waitForPriorityQueue.Len.spec (GF := GF) (hG := hG))
    (hLess : waitForPriorityQueue.Less.spec (GF := GF) (hG := hG))
    (hSwap : waitForPriorityQueue.Swap.spec (GF := GF) (hG := hG))
    (hPush : waitForPriorityQueue.Push.spec (GF := GF) (hG := hG))
    (pq : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ⊢
      heap.heapIface (interface.mk (go.GoType.PointerType (waitForPriorityQueue.ty T)) #pq)
        (wqHeap (K := K) pq) (wqElem (K := K) (T := T)) := by
  iintro #Hpkg
  iunfold heap.heapIface
  isplitr
  · iintro !> %xs
    wp_start as Hq
    iunfold wqHeap at Hq
    icases Hq with ⟨%s, Hqf, Hq⟩
    ihave %Hlen : ⌜(xs.length : Int) = sint.Z s.len⌝ $$ [Hq]
    · iunfold wqAt at Hq
      icases Hq with ⟨Hs, -, -⟩
      ihave %H := ownSlice_len s _ _ $$ Hs
      ipureintro; simp only [List.length_map] at H; word
    wp_auto
    wp_apply (hLen (K := K) (T := T) s)
    iapply HΦ
    isplitl
    · iunfold wqHeap; iexists s; iframe
    ipureintro; omega
  isplitr
  · iintro !> %xs %i %j
    wp_start as ⟨Hq, %Hb⟩
    iunfold wqHeap at Hq
    icases Hq with ⟨%s, Hqf, Hq⟩
    wp_auto
    wp_apply (hLess (K := K) (T := T) s xs i j Hb.1 Hb.2.1 Hb.2.2.1 Hb.2.2.2) $$ [$Hq] as %b Hq
    iapply HΦ
    iunfold wqHeap; iexists s; iframe
  isplitr
  · iintro !> %xs %i %j
    wp_start as ⟨Hq, %Hb⟩
    iunfold wqHeap at Hq
    icases Hq with ⟨%s, Hqf, Hq⟩
    wp_auto
    wp_apply (hSwap (K := K) (T := T) s xs i j Hb.1 Hb.2.1 Hb.2.2.1 Hb.2.2.2) $$ [$Hq] as Hq
    iapply HΦ
    iunfold wqHeap; iexists s; iframe
  · iintro !> %xs %x %a %Φ !> ⟨Hq, He⟩ HΦ
    iunfold wqHeap at Hq
    icases Hq with ⟨%s, Hqf, Hq⟩
    iunfold wqElem at He
    icases He with ⟨%Hx, %k, Hit⟩
    subst Hx
    wp_apply (hPush (K := K) (T := T) pq s xs a.1 a.2 k) $$ [$Hqf $Hq $Hit] as ⟨%s', Hqf, Hq⟩
    iapply HΦ
    iunfold wqHeap; iexists s'; iframe

/-- **`pq`'s `Pop`** over `wqHeap pq`. -/
theorem wq_heapPopIface
    (hPop : waitForPriorityQueue.Pop.spec (GF := GF) (hG := hG))
    (pq : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ⊢
      heap.heapPopIface (interface.mk (go.GoType.PointerType (waitForPriorityQueue.ty T)) #pq)
        (wqHeap (K := K) pq) (wqElem (K := K) (T := T)) := by
  iintro #Hpkg
  iunfold heap.heapPopIface
  iintro !> %xs %a %Φ !> Hq HΦ
  iunfold wqHeap at Hq
  icases Hq with ⟨%s, Hqf, Hq⟩
  wp_apply (hPop (K := K) (T := T) pq s xs a) $$ [$Hqf $Hq] as ⟨⟨%s', Hqf, Hq⟩, Ha⟩
  iapply HΦ
  isplitl [Hqf Hq]
  · iunfold wqHeap; iexists s'; iframe
  iunfold wqElem
  isplitr
  · ipureintro; rfl
  iexists _; iexact Ha

/-- `pq.Len()` through the pointer, on the heap: its number of entries. -/
theorem wqHeap_Len_of
    (hLen : waitForPriorityQueue.Len.spec (GF := GF) (hG := hG))
    (pq : Loc) (ws : List (Loc × K)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ wqHeap (K := K) pq ws }}
      (App (Val (pq @!! go.GoType.PointerType (waitForPriorityQueue.ty T) @!! go!"Len")) (Val #()))
    {{ RET #(W64 (ws.length : Int)); wqHeap (K := K) pq ws ∗ ⌜ws.length < 2 ^ 63⌝ }} := by
  wp_start as Hq
  iunfold wqHeap at Hq
  icases Hq with ⟨%s, Hqf, Hq⟩
  ihave %Hlen : ⌜ws.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len⌝ $$ [Hq]
  · iunfold wqAt at Hq
    icases Hq with ⟨Hs, -, -⟩
    ihave %H := ownSlice_len s _ _ $$ Hs
    ipureintro; simp only [List.length_map] at H; exact H
  wp_auto
  wp_apply (hLen (K := K) (T := T) s)
  rw [show s.len = W64 (ws.length : Int) by rw [Hlen.1]; word]
  iapply HΦ
  isplitl
  · iunfold wqHeap; iexists s; iframe
  ipureintro; rw [Hlen.1]; word

/-- `pq.Peek()` through the pointer, on a non-empty heap: its first entry. -/
theorem wqHeap_Peek_of
    (hPeek : waitForPriorityQueue.Peek.spec (GF := GF) (hG := hG))
    (pq : Loc) (a : Loc × K) (ws : List (Loc × K)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗
        wqHeap (K := K) pq (a :: ws) }}
      (App (Val (pq @!! go.GoType.PointerType (waitForPriorityQueue.ty T) @!! go!"Peek")) (Val #()))
    {{ RET #(interface.mkOk (go.GoType.PointerType (waitFor.ty T)) #a.1 : GoInterface);
        wqHeap (K := K) pq (a :: ws) }} := by
  wp_start as Hq
  iunfold wqHeap at Hq
  icases Hq with ⟨%s, Hqf, Hq⟩
  wp_auto
  wp_apply (hPeek (K := K) (T := T) s a ws) $$ [$Hq] as Hq
  iapply HΦ
  iunfold wqHeap; iexists s; iframe

/-- The first entry's `readyAt`, borrowed from the heap. -/
theorem wqHeap_first_readyAt (pq : Loc) (a : Loc × K) (ws : List (Loc × K)) :
    wqHeap (GF := GF) (K := K) pq (a :: ws) ⊢
      ∃ t : time.Time, structFieldRef (waitFor K) go!"readyAt" a.1 ↦ t ∗
        (structFieldRef (waitFor K) go!"readyAt" a.1 ↦ t -∗ wqHeap (K := K) pq (a :: ws)) := by
  iintro Hq
  iunfold wqHeap at Hq
  icases Hq with ⟨%s, Hqf, Hq⟩
  iunfold wqAt at Hq
  icases Hq with ⟨Hs, Hcap, Hits⟩
  icases BigSepL.bigSepL_cons.1 $$ Hits with ⟨Ha, Hits⟩
  iunfold wfAt at Ha
  icases Ha with ⟨#Hd, ⟨%t, Ht⟩, Hi⟩
  iexists t
  iframe Ht
  iintro Ht
  iunfold wqHeap; iexists s; iframe Hqf
  iunfold wqAt; iframe Hs Hcap
  iapply BigSepL.bigSepL_cons.2
  iframe Hits
  iunfold wfAt; iframe Hi; iframe #; iexists t; iexact Ht

end lemmas

end workqueue
end EtcdGrove
end Perennial
