/-
Proof of `Spec/Cache__WaitReady.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.Cache__WaitReady
import EtcdGrove.Cache.Spec.ready__WaitReady

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.WaitReady.wp_proof
    (wp_WaitReady : ready.WaitReady.spec (GF := GF) (hG := hG)) :
    Cache.WaitReady.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap e0 ctx s
  wp_start as ⟨Hc, #Hlb, #Hctx⟩
  iNamed Hc
  wp_auto
  wp_apply wp_WaitReady $$ [$HisReady $Hlb $Hctx] as %err Herr
  iapply HΦ $$ Herr

end proof

end EtcdGrove
end Perennial
