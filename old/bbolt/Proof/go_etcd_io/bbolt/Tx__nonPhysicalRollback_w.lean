module
public import Spec.go_etcd_io.bbolt.Tx__nonPhysicalRollback_w
public import Spec.go_etcd_io.bbolt.Tx__close_w
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
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

theorem Tx.nonPhysicalRollback.wp_wproof (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hclose : Tx.close.wspec (GF := GF) (hG := hG)) :
    Tx.nonPhysicalRollback.wspec (GF := GF) (hG := hG) := by
  intro I γ W txl txid σ T hRb hFC hPC hEW Hwr Htdb Hroot Hmtx
  wp_start as ⟨Hdbw, Hg, Hv⟩
  unfold dbWR
  icases Hdbw with ⟨Hdb, %Hdw⟩
  have Hdw' := Hdw
  obtain ⟨hAl, hrw, hdata, hps, hfli, w, hw, hwp, hwq, hwh, htx, htb⟩ := Hdw'
  subst htx
  icases ownDB_logger I W.dbl γ σ $$ Hdb with ⟨%lg, %dl, #Hlg, #Hdl, #Hdlok, %Hl, Hdb⟩
  have Hdbl := Hl.2
  icases ownDB_rollback I W.dbl γ σ w hw $$ Hdb with ⟨%fls, %hcan, Hfl, Hback⟩
  unfold ownWriteTxG
  icases Hg with ⟨Hrest, Hmv, Hpm, Hbufs, Hbs⟩
  unfold TxW_rest_root
  icases Hrest with ⟨Hwritable, Hmanaged, Htdbf, Hmetaf, Hpagesf, Hstatsf, Hch, HWF, %Htxlnn⟩
  unfold wView
  icases Hv with ⟨Hvd, #Hvps, #Hvlg, Hvfl, #Hvdl, %Hvlg', Hvpg⟩
  ihave #Hflpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist) $$ []
  · iPkgInit
  ihave #Hcpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common) $$ []
  · iPkgInit
  wp_auto
  rw [Htdb, decide_eq_false Hdbl]
  try wp_auto
  rw [Hwr]
  try wp_auto
  wp_apply hTxid T.t.meta' T.mv (DFrac.own 1) $$ [Hmv] as Hmv
  · iframe
  try wp_auto
  try rw [hfli]
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  rw [Hmtx]
  wp_apply hRb fls σ.fl _ hcan $$ [Hfl] as Hfl
  · iframe
  ihave Hdb := Hback $$ Hfl
  try wp_auto
  -- the transaction and its view as they were, the database rolled back
  ihave Hg : ownWriteTxG W txl T $$ [Hwritable Hmanaged Htdbf Hmetaf Hpagesf Hstatsf Hch HWF Hmv Hpm Hbufs Hbs]
  · unfold ownWriteTxG TxW_rest_root; rw [Hwr, Htdb]; iframe; ipureintro; exact Htxlnn
  ihave Hv : wView W $$ [Hvd Hvfl Hvpg]
  · unfold wView; rw [hfli]; iframe; iframe #; ipureintro; exact Hvlg'
  ihave Hdbw : dbWR I γ W txl (w.txid + W64 1) { σ with fl := σ.fl.rollback (w.txid + W64 1) } $$ [Hdb]
  · unfold dbWR; iframe; ipureintro; exact Hdw
  wp_apply hclose I γ W txl _ { σ with fl := σ.fl.rollback (w.txid + W64 1) } T w hFC hPC hEW hw
    (fun v0 v1 h => dbOK_removeWriter _ v0 v1 h w hw (rb_pending_none _ _))
    Hwr Htdb Hroot $$ [Hdbw Hg Hv] as ⟨%t, Hdb, Htx, %Ht⟩
  · iframe
  try wp_auto
  iapply HΦ
  iexists w, t
  iframe
  ipureintro; exact ⟨hw, Ht⟩

end proof

end bbolt
end EtcdGrove
end Perennial
