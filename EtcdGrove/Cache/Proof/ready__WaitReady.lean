/-
Proof of `Spec/ready__WaitReady.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.ready__WaitReady
import EtcdGrove.Cache.Spec.ready__waitForState

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem ready.WaitReady.wp_proof
    (wp_waitForState : ready.waitForState.spec (GF := GF) (hG := hG)) :
    ready.WaitReady.spec (GF := GF) (hG := hG) := by
  intro r γ e0 ctx s
  wp_start as ⟨#Hr, #Hlb, #Hctx⟩
  wp_auto
  ipersist r
  wp_func_lits
  wp_apply wp_waitForState r γ e0 ctx s _ id $$ [] as %err Herr
  · iframe #
    unfold readyPredSpec
    iintro %b
    wp_start as Hb
    wp_auto
    ihave H := HΦ $$ Hb
    iExactEq H
    rfl
  iapply HΦ $$ Herr

end proof

end EtcdGrove
end Perennial
