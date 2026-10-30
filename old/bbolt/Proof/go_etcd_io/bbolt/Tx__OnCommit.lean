module
public import Spec.go_etcd_io.bbolt.Tx__OnCommit

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

theorem Tx.OnCommit.wp_proof : Tx.OnCommit.spec (GF := GF) (hG := hG) := by
  intro tl t hs fn
  wp_start as ⟨Ht, Hs, Hcap⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs', Hcap', Hsl⟩
  try wp_auto
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
