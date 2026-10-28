/-
Proof of `Spec/k8s_io/client_go/util/workqueue/waitForPriorityQueue__Push.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Push

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem waitForPriorityQueue.Push.wp_proof : waitForPriorityQueue.Push.spec (GF := GF) (hG := hG) := by
  intro K T _ pq s ws w k i
  wp_start as ⟨Hpq, Hq, Hit⟩
  iunfold wqAt at Hq
  icases Hq with ⟨Hs, Hcap, Hits⟩
  ihave %Hlen := ownSlice_len s _ _ $$ Hs
  simp only [List.length_map] at Hlen
  iunfold wfAt at Hit
  icases Hit with ⟨#Hid, Ht, Hix⟩
  wp_auto
  wp_apply wp_slice_literal (V := Loc) [w]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_slice_append s (ws.map Prod.fst) _ [w] (DFrac.own 1) $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs', Hcap', -⟩
  iapply HΦ
  iexists s'
  iframe
  iunfold wqAt
  simp only [List.map_append, List.map_cons, List.map_nil]
  iframe Hs' Hcap'
  iapply BigSepL.bigSepL_snoc.2
  iframe Hits
  iunfold wfAt
  have hk : (W64 ((ws.length : Nat) : Int) : w64) = s.len := by rw [Hlen.1]; word
  rw [hk]
  iframe
  iframe #

end proof

end workqueue
end EtcdGrove
end Perennial
