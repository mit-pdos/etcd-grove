module
public import Spec.go_etcd_io.bbolt.internal.common.Verify
public import Spec.go_etcd_io.bbolt.internal.common.IsVerificationEnabled

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

theorem Verify.wp_proof (hE : IsVerificationEnabled.spec (GF := GF) (hG := hG)) :
    Verify.spec (GF := GF) (hG := hG) := by
  intro f Q
  wp_start as Hf
  wp_auto
  wp_apply hE as %b _
  wp_if_destruct
  · icases Hf with ⟨-, HQ⟩
    iapply HΦ $$ HQ
  · try wp_auto
    icases Hf with ⟨Hf, -⟩
    wp_bind (App (Val #f) (Val #()))
    iapply wp_wand $$ Hf
    iintro %v HQ
    wp_auto
    iapply HΦ $$ HQ

end proof

end bbolt
end EtcdGrove
end Perennial
