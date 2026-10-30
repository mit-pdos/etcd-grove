module
public import Spec.go_etcd_io.bbolt.DB__Sync
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.fdatasync

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

theorem DB.Sync.wp_proof
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hfdatasync : fdatasync.spec (GF := GF) (hG := hG)) :
    DB.Sync.spec (GF := GF) (hG := hG) := by
  intro dbl f fd dq lg dl Hdbl Hlg
  wp_start as ⟨Hlgf, #Hdl, Hf, #Hfile⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply hLogger dbl dq lg dl Hdbl $$ [Hlgf Hdl] as Hlgf
  · iframe; iexact Hdl
  have Hd : (if lg = interface.nil then discardIface dl else lg) = discardIface dl := by
    rcases Hlg with rfl | rfl <;> simp [discardIface, interface.mkOk]
  rw [Hd]
  try wp_auto
  wp_apply hfdatasync dbl f fd dq $$ [Hf Hfile] as %err Hf
  · iframe; iframe #
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
