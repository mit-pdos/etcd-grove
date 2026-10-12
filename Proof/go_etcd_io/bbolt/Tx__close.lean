module
public import Spec.go_etcd_io.bbolt.Tx__close
public import Proof.go_etcd_io.bbolt.DBAcc

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

variable [AllG GF]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem Tx.close.wp_proof (hremove : DB.removeTx.spec (GF := GF) (hG := hG)) :
    Tx.close.spec (GF := GF) (hG := hG) := by
  intro I dbl γ σ txl k r m hRem
  wp_start as ⟨Hdb, Hrtx⟩
  icases ownDB_logger I dbl γ σ $$ Hdb with ⟨%lg, %dl, Hlg, #Hdl, #Hdlok, %Hl, Hback⟩
  ihave Hdb := Hback $$ Hlg
  have Hdbl := Hl.2
  simp only [ownReadTx]
  iNamed Hrtx
  have Ht' := Ht
  obtain ⟨Htdb, Htw, _⟩ := Ht'
  wp_auto
  rw [Htdb, decide_eq_false Hdbl]
  try wp_auto
  rw [Htw]
  try wp_auto
  ihave Hrtx : ownReadTx dbl γ txl k r σ.data σ.ps m $$ [Htx Hmeta Hroot Hrdata Hrps Hpages Hrl Hkey]
  · simp only [ownReadTx]; iexists t, mv; iframe; ipureintro; exact Ht
  rw [Htdb]
  wp_apply hremove I dbl γ σ txl k r m hRem $$ [Hdb Hrtx] as ⟨%ro, %t', %Hk, Hdb, Htx, %Ht'⟩
  · iframe
  try wp_auto
  iapply HΦ
  iexists ro, _
  iframe
  ipureintro; exact ⟨Hk, rfl⟩

end proof

end bbolt
end EtcdGrove
end Perennial
