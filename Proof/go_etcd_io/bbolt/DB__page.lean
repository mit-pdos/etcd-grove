module
public import Spec.go_etcd_io.bbolt.DB__page
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

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

theorem DB.page.wp_proof : DB.page.spec (GF := GF) (hG := hG) := by
  intro dbl data ps dq id Hc Hlt
  wp_start as ⟨Hd, Hps⟩
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩), arrayIndexRef_w8 (hG := hG) _ _ Hc,
    show sint.Z (id * ps) = uint.Z (id * ps) by word]
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
