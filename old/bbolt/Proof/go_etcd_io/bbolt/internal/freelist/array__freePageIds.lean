module
public import Spec.go_etcd_io.bbolt.internal.freelist.array__freePageIds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem array.freePageIds.wp_proof : array.freePageIds.spec (GF := GF) (hG := hG) := by
  intro a s free
  wp_start as Ha
  iNamed Ha
  wp_auto
  iapply HΦ
  iframe
  iintro Hids
  unfold ownArrayPart
  iexists ids
  iframe
  ipureintro; exact Hincr

end proof

end bbolt
end EtcdGrove
end Perennial
