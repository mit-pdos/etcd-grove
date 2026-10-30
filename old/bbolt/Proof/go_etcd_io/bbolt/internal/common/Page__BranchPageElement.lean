module
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Page.BranchPageElement.wp_proof (hUnsafeIndex : UnsafeIndex.spec (GF := GF) (hG := hG)) :
    Page.BranchPageElement.spec (GF := GF) (hG := hG) := by
  intro l i
  wp_start
  wp_auto
  wp_apply hUnsafeIndex
  rw [show sint.Z (W64 16 + W64 (uint.Z i) * W64 16) = 16 + 16 * uint.Z i by word]
  iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
