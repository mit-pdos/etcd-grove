module
public import Spec.go_etcd_io.bbolt.Tx__rollback_l
public import Spec.go_etcd_io.bbolt.Tx__close_l
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Proof.go_etcd_io.bbolt.DBAcc
public import Proof.go_etcd_io.bbolt.DBRollback

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem Tx.rollback.wp_lproof (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hclose : Tx.close.lspec (GF := GF) (hG := hG)) :
    Tx.rollback.lspec (GF := GF) (hG := hG) := by
  intro I W txl txid fl T hRb hFC hPC hEW Hwr Htdb Hroot Hmtx
  wp_start as ⟨Hdbl, Hg⟩
  unfold dbLost
  icases Hdbl with ⟨%fls, %sp, %ps, %Hl, Hfl, Hdata, Hflf, Hrwtx, #Hps, #Hrwlock, Hrwl, Hstath,
    Hstatsf0, Hstats⟩
  obtain ⟨hcan, Hdbl⟩ := Hl
  unfold ownWriteTxG
  icases Hg with ⟨Hrest, Hmv, Hpm, Hbufs, Hbs⟩
  unfold TxW_rest_root
  icases Hrest with ⟨Hwritable, Hmanaged, Htdbf, Hmetaf, Hpagesf, Hstatsf, Hch, HWF, %Htxlnn⟩
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
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  rw [Hmtx]
  wp_apply hRb fls fl _ hcan $$ [Hfl] as Hfl
  · iframe
  try wp_auto
  -- `data` is nil: no reload
  wp_apply hclose I W txl txid (fl.rollback txid) T hFC hPC hEW Hwr Htdb Hroot
    $$ [Hfl Hdata Hflf Hrwtx Hrwl Hstath Hstatsf0 Hstats Hwritable Hmanaged Htdbf Hmetaf Hpagesf
      Hstatsf Hch HWF Hmv Hpm Hbufs Hbs] as ⟨%t, Htx, %Ht⟩
  · iframe
    isplitr [Hwritable Hmanaged Htdbf Hmetaf Hpagesf Hstatsf Hch HWF Hmv Hpm Hbufs Hbs]
    · unfold dbLost
      iexists fls, sp, ps
      iframe
      iframe #
      ipureintro; exact ⟨fun pd h => absurd rfl (rb_pending _ _ _ _ h).1, Hdbl⟩
    unfold ownWriteTxG TxW_rest_root
    try rw [Htdb]
    try rw [Hwr]
    iframe
    ipureintro; exact Htxlnn
  try wp_auto
  iapply HΦ
  iexists t
  iframe
  ipureintro; exact Ht

end proof

end bbolt
end EtcdGrove
end Perennial
