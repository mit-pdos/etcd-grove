/-
Proof of `Spec/probeItemFromKey.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.probeItemFromKey

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem probeItemFromKey.wp_proof : probeItemFromKey.spec (GF := GF) (hG := hG) := by
  intro sl key dq
  simp only [kvItemIs]
  wp_start as Hsl
  wp_auto
  wp_apply wp_bytes_to_string sl key dq $$ Hsl as Hsl
  wp_alloc p as Hp
  ipersist Hp
  wp_end
  iframe Hsl Hp

end proof

end EtcdGrove
end Perennial
