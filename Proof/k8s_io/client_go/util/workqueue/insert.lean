/-
Proof of `Spec/k8s_io/client_go/util/workqueue/insert.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.insert
public import Spec.container.heap.Fix
public import Spec.container.heap.Push
public import Proof.k8s_io.client_go.util.workqueue.DelayingLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem insert.wp_proof
    (wp_Fix : heap.Fix.spec (GF := GF) (hG := hG))
    (wp_Push : heap.Push.spec (GF := GF) (hG := hG))
    (hLen : waitForPriorityQueue.Len.spec (GF := GF) (hG := hG))
    (hLess : waitForPriorityQueue.Less.spec (GF := GF) (hG := hG))
    (hSwap : waitForPriorityQueue.Swap.spec (GF := GF) (hG := hG))
    (hPush : waitForPriorityQueue.Push.spec (GF := GF) (hG := hG)) :
    insert.spec (GF := GF) (hG := hG) := by
  intro K T _ pq ws m mm w wf Hok
  wp_start as ⟨Hq, Hm, Hw⟩
  have hh := wq_heapIface (K := K) (T := T) @hLen @hLess @hSwap @hPush pq
  ihave #Hheap := hh $$ Hpkg
  iStructNamed Hw
  wp_auto
  wp_apply wp_map_lookup2 (V := Loc) T (go.GoType.PointerType (waitFor.ty T)) m mm wf.data' _ $$ Hm as Hm
  cases hk : mm !! wf.data'
  · -- a new item: pushed
    simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
    wp_auto
    ipersist data
    wp_apply (wp_Push (Loc × K) (interface.mk (go.GoType.PointerType (waitForPriorityQueue.ty T)) #pq)
      (wqHeap (K := K) pq) (wqElem (K := K) (T := T)) ws
      (interface.mkOk (go.GoType.PointerType (waitFor.ty T)) #w) (w, wf.data'))
      $$ [$Hheap $Hq data readyAt index] as ⟨%ys, Hq, %Hys⟩
    · iunfold wqElem
      isplitr
      · ipureintro; rfl
      iexists wf.index'
      iunfold wfAt
      iframe
      iframe #
    wp_apply wp_mapInsert $$ Hm as Hm
    iapply HΦ
    iexists ys, _
    iframe
    ipureintro
    exact byDataOk_insert w wf.data' Hok hk Hys
  · -- already waiting
    rename_i e
    have hin : (e, wf.data') ∈ ws := (Hok.2 wf.data' e).1 hk
    obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hin
    have hpl : ws[p]? = some (e, wf.data') := by rw [List.getElem?_eq_getElem hp, hpe]
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    wp_auto
    iunfold wqHeap at Hq
    icases Hq with ⟨%s, Hqf, Hq⟩
    iunfold wqAt at Hq
    icases Hq with ⟨Hs, Hcap, Hits⟩
    ihave %Hlen := ownSlice_len s _ _ $$ Hs
    simp only [List.length_map] at Hlen
    icases (BigSepL.bigSepL_lookup_acc hpl).1 $$ Hits with ⟨He, Hits⟩
    iunfold wfAt at He
    icases He with ⟨#Hed, ⟨%te, Het⟩, Hei⟩
    wp_apply Time.wp_ptr_After_dq $$ [$Het] as %b Het
    cases b
    · -- not later: nothing changes
      wp_auto
      iapply HΦ
      iexists ws, mm
      iframe
      isplitl
      · iunfold wqHeap
        iexists s
        iframe
        iunfold wqAt
        iframe
        ihave Hits := Hits $$ [Hed Het Hei]
        · iunfold wfAt; iframe; iframe #
        rw [list_set_lookup_self ws p _ hpl]
        iexact Hits
      ipureintro; exact Hok
    · -- earlier: moved, and the heap fixed
      wp_auto
      ihave Hits := Hits $$ [Hed Het Hei]
      · iunfold wfAt; iframe; iframe #; iexists _; iexact Het
      rw [list_set_lookup_self ws p _ hpl]
      have hp0 : 0 ≤ sint.Z (W64 (p : Int)) := by word
      have hp1 : sint.Z (W64 (p : Int)) < ws.length := by word
      wp_apply (wp_Fix (Loc × K) (interface.mk (go.GoType.PointerType (waitForPriorityQueue.ty T)) #pq)
        (wqHeap (K := K) pq) (wqElem (K := K) (T := T)) ws (W64 (p : Int)) hp0 hp1)
        $$ [$Hheap Hqf Hs Hcap Hits] as ⟨%ys, Hq, %Hys⟩
      · iunfold wqHeap; iexists s; iframe; iunfold wqAt; iframe
      iapply HΦ
      iexists ys, mm
      iframe
      ipureintro
      exact byDataOk_perm Hok Hys

end proof

end workqueue
end EtcdGrove
end Perennial
