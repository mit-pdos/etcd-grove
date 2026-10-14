/-
Proof of `Spec/Cache__WaitReady.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__WaitReady
public import Spec.go_etcd_io.etcd.cache.v3.ready__WaitReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
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
