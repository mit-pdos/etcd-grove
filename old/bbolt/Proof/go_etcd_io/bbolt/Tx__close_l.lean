module
public import Spec.go_etcd_io.bbolt.Tx__close_l
public import Spec.go_etcd_io.bbolt.TxStats__add
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

theorem lost_Stats_join (l : Loc) (dq : DFrac) (v : Stats) (x : TxStats) :
    structFieldRef Stats go!"TxStats" l ↦{dq} x ∗ Stats_rest_TxStats (GF := GF) l dq v ⊢
      l ↦{dq} ({ v with TxStats' := x } : Stats) :=
  (Stats_split_TxStats l dq { v with TxStats' := x }).2

theorem lost_Tx_join (txl : Loc) (rv : Bucket) (v : Tx) :
    structFieldRef Tx go!"root" txl ↦ rv ∗ TxW_rest_root (GF := GF) txl (DFrac.own 1) v ⊢
      txl ↦ ({ v with root' := rv } : Tx) :=
  (TxW_split_root txl (DFrac.own 1) { v with root' := rv }).2

theorem Tx.close.wp_lproof (hadd : TxStats.add.spec (GF := GF) (hG := hG)) :
    Tx.close.lspec (GF := GF) (hG := hG) := by
  intro I W txl txid fl T hFC hPC hEW Hwr Htdb Hroot
  wp_start as ⟨Hdbl, Hg⟩
  unfold dbLost
  icases Hdbl with ⟨%fls, %sp, %ps, %Hl, Hfl, Hdata, Hflf, Hrwtx, #Hps, #Hrwlock, Hrwl, Hstath,
    Hstatsf0, Hstats⟩
  obtain ⟨-, Hdbl⟩ := Hl
  unfold ownWriteTxG
  icases Hg with ⟨Hrest, Hmv, Hpm, Hbufs, Hbs⟩
  unfold TxW_rest_root
  icases Hrest with ⟨Hwritable, Hmanaged, Htdbf, Hmetaf, Hpagesf, Hstatsf, Hch, HWF, %Htxlnn⟩
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 Hroot
  icases (BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun bl B => bktOwn (GF := GF) W bl B) hB).1 $$ Hbs with ⟨HB, -⟩
  unfold bktOwn
  icases HB with ⟨Hbv, -, -, -, -, -⟩
  ihave #Hflpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist) $$ []
  · iPkgInit
  wp_auto
  rw [Htdb, decide_eq_false Hdbl]
  try wp_auto
  rw [Hwr]
  try wp_auto
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  wp_apply hFC fls fl $$ [Hfl] as Hfl
  · iframe
  try wp_auto
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  wp_apply hPC fls fl $$ [Hfl] as Hfl
  · iframe
  try wp_auto
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  wp_apply hEW fls fl $$ [Hfl] as Hfl
  · iframe
  try wp_auto
  -- the write lock released
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hrwlock $Hrwl]
  · iframe; inext; itrivial
  try wp_auto
  -- the statistics merged
  icases Hstats with (%Hsn | ⟨%sv, Hsv⟩)
  focus
    rw [decide_eq_true Hsn]
    try wp_auto
  rotate_left
  focus
    icases typedPointsto_not_null_dup _ _ _ $$ Hsv with ⟨Hsv, %Hsnn⟩
    rw [decide_eq_false Hsnn]
    try wp_auto
    wp_apply sync.RWMutex.wp_Lock _ _ $$ [$Hstath] as ⟨Hsl, -⟩
    try wp_auto
    try simp only
    icases (Stats_split_TxStats _ _ _).1 $$ Hsv with ⟨HsT, Hsr⟩
    wp_apply hadd _ _ _ _ (DFrac.own 1) $$ [HsT Hstatsf] as %v' ⟨%Hv', HsT, Hstatsf⟩
    · iframe
    try wp_auto
    wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hsl] as Hstath
    · iframe; simp only [statsInv]; inext; itrivial
    try wp_auto
  all_goals
    try wp_auto
    -- the transaction, its references cleared
    ihave Hrest : TxW_rest_root txl (DFrac.own 1)
        ({ T.t with db' := null, meta' := null, pages' := null, writable' := true } : Tx)
      $$ [Hwritable Hmanaged Htdbf Hmetaf Hpagesf Hstatsf Hch HWF]
    · unfold TxW_rest_root; iframe; ipureintro; exact Htxlnn
    ihave Htx := lost_Tx_join _ _ _ $$ [Hbv Hrest]
    · iframe
    iapply HΦ
    iexists _
    iframe
    ipureintro; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
