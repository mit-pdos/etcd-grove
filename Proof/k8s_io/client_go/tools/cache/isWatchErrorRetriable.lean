/-
Proof of `Spec/k8s_io/client_go/tools/cache/isWatchErrorRetriable.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.isWatchErrorRetriable
public import Spec.k8s_io.apimachinery.pkg.util.net.IsConnectionRefused
public import Spec.k8s_io.apimachinery.pkg.api.errors.IsTooManyRequests

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem isWatchErrorRetriable.wp_proof
    (wp_IsConnectionRefused : net.IsConnectionRefused.spec (GF := GF) (hG := hG))
    (wp_IsTooManyRequests : apierrors.IsTooManyRequests.spec (GF := GF) (hG := hG)) :
    isWatchErrorRetriable.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start
  ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.net $$ []
  · iPkgInit
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_IsConnectionRefused err) $$ [$Hnet] as %b1 -
  (try wp_auto)
  rcases b1 with _ | _
  · (try wp_auto)
    wp_apply (wp_IsTooManyRequests err) $$ [$Herrs] as %b2 -
    (try wp_auto)
    rcases b2 with _ | _ <;> (try wp_auto) <;> (iapply HΦ; itrivial)
  · (try wp_auto)
    iapply HΦ
    itrivial

end proof

end cache
end EtcdGrove
end Perennial
