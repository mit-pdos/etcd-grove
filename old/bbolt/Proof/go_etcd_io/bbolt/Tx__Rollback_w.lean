module
public import Spec.go_etcd_io.bbolt.Tx__Rollback_w
public import Spec.go_etcd_io.bbolt.internal.common.Assert
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem Tx.Rollback.wp_wproof (hAssert : Assert.spec (GF := GF) (hG := hG))
    (hrb : Tx.nonPhysicalRollback.wspec (GF := GF) (hG := hG)) :
    Tx.Rollback.wspec (GF := GF) (hG := hG) := by
  intro I γ W txl txid σ T hRb hFC hPC hEW Hwr Hman Htdb Hroot Hmtx
  wp_start as ⟨Hdbw, Hg, Hv⟩
  unfold dbWR
  icases Hdbw with ⟨Hdb, %Hdw⟩
  icases ownDB_logger I W.dbl γ σ $$ Hdb with ⟨%lg, %dl, #Hlg, #Hdl, #Hdlok, %Hl, Hdb⟩
  have Hdbl := Hl.2
  unfold ownWriteTxG
  icases Hg with ⟨Hrest, Hmv, Hpm, Hbufs, Hbs⟩
  unfold TxW_rest_root
  icases Hrest with ⟨Hwritable, Hmanaged, Htdbf, Hmetaf, Hpagesf, Hstatsf, Hch, HWF, %Htxlnn⟩
  wp_auto
  rw [Hman]
  try wp_auto
  wp_apply hAssert
  try wp_auto
  rw [Htdb, decide_eq_false Hdbl]
  try wp_auto
  ihave Hg : ownWriteTxG W txl T $$ [Hwritable Hmanaged Htdbf Hmetaf Hpagesf Hstatsf Hch HWF Hmv Hpm Hbufs Hbs]
  · unfold ownWriteTxG TxW_rest_root; rw [Hman, Htdb]; iframe; ipureintro; exact Htxlnn
  ihave Hdbw : dbWR I γ W txl txid σ $$ [Hdb]
  · unfold dbWR; iframe; ipureintro; exact Hdw
  wp_apply hrb I γ W txl txid σ T hRb hFC hPC hEW Hwr Htdb Hroot Hmtx $$ [Hdbw Hg Hv] as Hpost
  · iframe
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
