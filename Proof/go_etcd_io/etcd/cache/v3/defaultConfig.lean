/-
Proof of `Spec/defaultConfig.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.defaultConfig

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem defaultConfig.wp_proof : defaultConfig.spec (GF := GF) (hG := hG) := by
  wp_start
  try wp_auto
  have h : Config.mk (W64 10) (W64 2048) (W64 50 * W64 1000000) (W64 50 * W64 1000000)
      (W64 2 * W64 1000000000) (W64 5 * W64 1000000000) (W64 3 * W64 1000000000) (W64 32)
      (W64 100 * W64 1000000) (W64 10 * W64 60000000000) = defaultConfigVal := by
    unfold defaultConfigVal; rfl
  rw [h]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
