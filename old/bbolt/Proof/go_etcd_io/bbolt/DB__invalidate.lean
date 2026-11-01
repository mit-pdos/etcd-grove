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
  intro dbl dr dp ds m0 m1
  wp_start as ⟨Hdr, Hdp, Hds, Hm0, Hm1⟩
  wp_auto
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
