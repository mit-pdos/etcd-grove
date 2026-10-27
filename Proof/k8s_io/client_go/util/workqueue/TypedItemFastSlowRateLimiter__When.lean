/-
Proof of `Spec/k8s_io/client_go/util/workqueue/TypedItemFastSlowRateLimiter__When.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.TypedItemFastSlowRateLimiter__When

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

theorem TypedItemFastSlowRateLimiter.When.wp_proof : TypedItemFastSlowRateLimiter.When.spec (GF := GF) (hG := hG) := by
  intro K T _ r fast slow k
  wp_start as #Hr
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isFastSlowLimiter at Hr
  icases Hr with ⟨%fm, %n, #Hfm, #Hn, #Hfast, #Hslow, #Hmu⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iunfold failuresInv at HI
  icases HI with ⟨%mv, Hm⟩
  (try wp_auto)
  wp_apply wp_map_lookup1 (V := w64) T go.int fm mv k _ $$ Hm as Hm
  wp_apply wp_mapInsert $$ Hm as Hm
  wp_apply wp_map_lookup1 (V := w64) T go.int fm _ k _ $$ Hm as Hm
  wp_if_destruct
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm]
    · inext; iunfold failuresInv; iexists _; iframe
    iapply HΦ; ipureintro; exact Or.inl rfl
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm]
    · inext; iunfold failuresInv; iexists _; iframe
    iapply HΦ; ipureintro; exact Or.inr rfl

end proof

end workqueue
end EtcdGrove
end Perennial
