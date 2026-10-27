/-
Proof of `Spec/k8s_io/client_go/util/workqueue/TypedItemExponentialFailureRateLimiter__When.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.TypedItemExponentialFailureRateLimiter__When
public import Spec.time.Duration__Nanoseconds_ptr
public import Spec.math.Pow
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.FloatToInt
public import Proof.k8s_io.client_go.util.workqueue.UntypedIntToFloat

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

theorem TypedItemExponentialFailureRateLimiter.When.wp_proof [EtcdGrove.Float64ToInt64Semantics] [EtcdGrove.UntypedIntToFloat64Semantics]
    (wp_Nanoseconds : time.Duration.Nanoseconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Pow : math.Pow.spec (GF := GF) (hG := hG)) :
    TypedItemExponentialFailureRateLimiter.When.spec (GF := GF) (hG := hG) := by
  intro K T _ r max k
  wp_start as #Hr
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isExpLimiter at Hr
  icases Hr with ⟨%fm, %base, #Hfm, #Hbase, #Hmax, #Hmu⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iunfold failuresInv at HI
  icases HI with ⟨%mv, Hm⟩
  (try wp_auto)
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hmath : isPkgInit (PROP := IProp GF) pkg_id.math $$ []
  · iPkgInit
  wp_apply wp_map_lookup1 (V := w64) T go.int fm mv k _ $$ Hm as Hm
  wp_apply wp_map_lookup1 (V := w64) T go.int fm mv k _ $$ Hm as Hm
  wp_apply wp_mapInsert $$ Hm as Hm
  wp_apply wp_Nanoseconds $$ [$Hbase] as -
  wp_apply wp_Pow as %p -
  generalize (float64Mul (int64ToFloat64 base) p) = bf
  generalize (untypedIntToFloat64 9223372036854775807) = mf
  cases hb : (float64Leb mf bf && !decide (bf = mf))
  · -- not above `MaxInt64`: the conversion
    wp_auto
    wp_if_destruct
    · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm]
      · inext; iunfold failuresInv; iexists _; iframe
      iapply HΦ; ipureintro; exact Int.le_refl _
    · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm]
      · inext; iunfold failuresInv; iexists _; iframe
      iapply HΦ; ipureintro; omega
  · -- above: `maxDelay`
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm]
    · inext; iunfold failuresInv; iexists _; iframe
    iapply HΦ; ipureintro; exact Int.le_refl _

end proof

end workqueue
end EtcdGrove
end Perennial
