module
public import Spec.go_etcd_io.bbolt.Tx__Cursor
public import Spec.go_etcd_io.bbolt.Bucket__Cursor

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

theorem Tx.Cursor.wp_proof (hCursor : Bucket.Cursor.spec (GF := GF) (hG := hG)) :
    Tx.Cursor.spec (GF := GF) (hG := hG) := by
  intro txl V q
  wp_start as ⟨Hctx, Hpgs, Hst⟩
  wp_auto
  wp_apply hCursor _ V q $$ [Hctx Hpgs Hst] as %cl ⟨Hc, Hst⟩
  · iframe
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
