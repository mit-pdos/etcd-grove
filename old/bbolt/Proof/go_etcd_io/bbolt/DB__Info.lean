module
public import Spec.go_etcd_io.bbolt.DB__Info
public import Spec.go_etcd_io.bbolt.internal.common.Assert
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

theorem DB.Info.wp_proof (hAssert : _root_.Perennial.EtcdGrove.bbolt.Assert.spec (GF := GF) (hG := hG)) :
    DB.Info.spec (GF := GF) (hG := hG) := by
  intro dbl d dq Hnn
  wp_start as Hl
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  rw [decide_eq_false Hnn]
  try wp_auto
  wp_apply hAssert
  try wp_auto
  rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero]
  wp_alloc p as Hp
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
