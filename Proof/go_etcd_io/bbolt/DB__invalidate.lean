module
public import Spec.go_etcd_io.bbolt.DB__invalidate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.invalidate.wp_proof : DB.invalidate.spec (GF := GF) (hG := hG) := by
  intro dbl d
  wp_start as Hl
  wp_auto
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
