module
public import Spec.go_etcd_io.bbolt.Tx__Bucket

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

theorem Tx.Bucket.wp_proof (hBucket : Bucket.Bucket.spec (GF := GF) (hG := hG)) :
    Tx.Bucket.spec (GF := GF) (hG := hG) := by
  intro txl V q name nb dn Hbm Hwr
  wp_start as ⟨HR, Hst, Hn⟩
  wp_auto
  wp_apply hBucket _ V q name nb dn Hbm Hwr $$ [HR Hst Hn] as %cl Hpost
  · iframe
  iapply HΦ $$ Hpost

end proof

end bbolt
end EtcdGrove
end Perennial
