/-
Proof of `Spec/k8s_io/client_go/util/workqueue/TypedItemExponentialFailureRateLimiter__NumRequeues.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.TypedItemExponentialFailureRateLimiter__NumRequeues

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

theorem TypedItemExponentialFailureRateLimiter.NumRequeues.wp_proof : TypedItemExponentialFailureRateLimiter.NumRequeues.spec (GF := GF) (hG := hG) := by
  intro K T _ r max k
  wp_start as #Hr
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isExpLimiter at Hr
  icases Hr with ⟨%fm, %base, #Hfm, #Hbase, #Hmax, #Hmu⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iunfold failuresInv at HI
  icases HI with ⟨%mv, Hm⟩
  (try wp_auto)
  wp_apply wp_map_lookup1 (V := w64) T go.int fm mv k (DFrac.own 1) $$ Hm as Hm
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm]
  · inext; iunfold failuresInv; iexists _; iframe
  wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
