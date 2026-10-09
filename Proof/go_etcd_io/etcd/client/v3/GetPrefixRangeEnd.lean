/-
Proof of `Spec/GetPrefixRangeEnd.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.GetPrefixRangeEnd
public import Spec.go_etcd_io.etcd.client.v3.getPrefix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem GetPrefixRangeEnd.wp_proof (wp_getPrefix : getPrefix.spec (GF := GF) (hG := hG)) :
    GetPrefixRangeEnd.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  wp_auto
  wp_apply wp_string_to_bytes p as %sl ⟨Hsl, -⟩
  wp_apply wp_getPrefix $$ [$Hsl] as %out ⟨-, #Hout⟩
  wp_apply wp_bytes_to_string $$ Hout as -
  wp_end

end proof

end EtcdGrove
end Perennial
