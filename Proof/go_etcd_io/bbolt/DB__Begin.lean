module
public import Spec.go_etcd_io.bbolt.DB__Begin
public import Spec.go_etcd_io.bbolt.DB__beginTx
public import Spec.go_etcd_io.bbolt.DB__Logger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem DB.Begin.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hbegin : DB.beginTx.spec (GF := GF) (hG := hG)) :
    DB.Begin.spec (GF := GF) (hG := hG) := by
  intro I dbl γ σ hAdd hsize
  wp_start as Hdb
  icases ownDB_logger I dbl γ σ $$ Hdb with ⟨%lg, %dl, Hlg, #Hdl, #Hdlok, %Hl, Hback⟩
  obtain ⟨Hlg', Hdbl⟩ := Hl
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply hLogger dbl (DFrac.own 1) lg dl Hdbl $$ [Hlg Hdl] as Hlg
  · iframe; iexact Hdl
  have Hd : (if lg = interface.nil then discardIface dl else lg) = discardIface dl := by
    rcases Hlg' with rfl | rfl <;> simp [discardIface, interface.mkOk]
  rw [Hd]
  try wp_auto
  ihave Hdb := Hback $$ Hlg
  wp_apply hbegin I dbl γ σ hAdd hsize $$ [Hdb] as %txl Hpost
  · iframe
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
