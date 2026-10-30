module
public import Spec.go_etcd_io.bbolt.node__free_x
public import Spec.go_etcd_io.bbolt.Tx__page_w
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Proof.go_etcd_io.bbolt.RebalanceDB
public import Proof.go_etcd_io.bbolt.DBFree
public import Proof.go_etcd_io.bbolt.DBAcc
public import Proof.go_etcd_io.bbolt.WriteCursorLemmas

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

theorem freex_uZ (pgid : w64) (ps : Nat) (hps : ps < 2 ^ 32)
    (h : uint.nat pgid * ps < 281474976710655) :
    uint.Z (pgid * W64 (ps : Int)) = ((uint.nat pgid * ps : Nat) : Int) := by
  have hu : uint.Z (pgid * W64 (ps : Int)) = (uint.Z pgid * uint.Z (W64 (ps : Int))) % 2 ^ 64 := by
    unfold uint.Z; rw [BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]; rfl
  have e1 : uint.Z pgid = ((uint.nat pgid : Nat) : Int) := by unfold uint.nat uint.Z; simp
  have e2 : uint.Z (W64 (ps : Int)) = (ps : Int) := by word
  rw [hu, e1, e2, ← Int.natCast_mul]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem freex_ov (pg : List w8) :
    uint.nat (pageOf pg).overflow' + 1 = 1 + pageOverflow pg := by
  have := pageOverflow_lt pg
  simp only [pageOf]
  have : uint.nat (W32 ((pageOverflow pg : Nat) : Int)) = pageOverflow pg := by
    unfold uint.nat; rw [toNat_W32 _ this]
  omega

open Classical in
theorem node.free.wp_xproof (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hpage : Tx.page.wspec (GF := GF) (hG := hG)) :
    node.free.xspec (GF := GF) (hG := hG) := by
  intro I γd γ W hwm txl txid ρ bl bv dqb pmap pm mp mv dqt F nl nv hFree HvOK Htx Hbl Hmtx HF Hwf
  wp_start as ⟨Hn, Hb, Hv, Hpf, Hpm, Hdbf, Hmf, Hmv, Hdbw, HFt, Htok⟩
  by_cases h0 : nv.pgid' = W64 0
  · rcases nv with ⟨b0, il, ub, sp, k, pg0, par, ch, ins⟩
    simp only at h0
    subst h0
    wp_auto
    iapply HΦ
    iexists ρ, F
    iframe
    ipureintro; exact ⟨HF, ⟨ρ.fl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩
  · wp_auto
    rw [decide_eq_false h0]
    try wp_auto
    rw [if_neg h0]
    obtain ⟨Hwf', Hpmn⟩ := Hwf h0
    obtain ⟨pg, Hpg⟩ : ∃ pg, W.pages !! uint.nat nv.pgid' = some pg := by
      cases Hwf' with
      | page _ pg _ hpg _ _ => exact ⟨pg, hpg⟩
    obtain ⟨Hl16, Hid, -, Hk⟩ := treeWF_page _ _ _ pg Hwf' Hpg
    icases dbWR_view_keep I γd W txl txid ρ $$ Hdbw with ⟨Hdbw, %Hdisj⟩
    icases pgToks_fresh γ F _ $$ [HFt Htok] with ⟨HFt, Htok, %HFn⟩
    · iframe
    ihave #Hcom : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common) $$ []
    · iPkgInit
    ihave #Hflpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist) $$ []
    · iPkgInit
    rw [Hbl]
    try wp_auto
    rw [Htx]
    try wp_auto
    wp_apply hTxid mp mv (DFrac.own 1) $$ [Hmv] as Hmv
    · iframe
    try wp_auto
    rw [Hbl]
    try wp_auto
    rw [Htx]
    try wp_auto
    -- the page, out of the view
    have Hps32 := HvOK.2.2.1
    have Hlt := HvOK.2.2.2.1 _ pg Hpg
    have HuZ := freex_uZ nv.pgid' W.ps Hps32 Hlt
    unfold wView
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    icases viewLoc_acc W _ pg (inViewLoc_page W _ pg Hpg) $$ Hpv with ⟨Hpgb, Hpvback⟩
    have Hloc : W.data +ₗ ((uint.nat nv.pgid' * W.ps : Nat) : Int) =
        W.data +ₗ uint.Z (nv.pgid' * W64 (W.ps : Int)) := by rw [HuZ]
    have Hcar : (W.data +ₗ ((uint.nat nv.pgid' * W.ps : Nat) : Int)).locCar ≠ 0 := by
      simpa [Loc.add] using HvOK.1
    have Hfl : validPageFlags (W16 (pageFlags pg : Int)) :=
      validPageFlags_of pg (by rcases Hk with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])
    have Hidw : W64 (pageId pg : Int) = nv.pgid' := by rw [Hid]; unfold uint.nat; word
    wp_apply hpage txl pmap pm dqt dqt W.dbl W.data (W64 (W.ps : Int))
      (DFrac.own W.q) DFrac.discard nv.pgid' (W.data +ₗ ((uint.nat nv.pgid' * W.ps : Nat) : Int))
      (DFrac.own W.q) pg (Or.inr ⟨Hpmn, Hloc, HvOK.1, by rw [HuZ]; push_cast; omega⟩) Hcar Hl16 Hidw Hfl
      $$ [Hpf Hpm Hdbf Hdata Hpgb] as ⟨Hpf, Hpm, Hdbf, Hdata, -, Hpgb⟩
    · iframe; iframe #
    try wp_auto
    rw [Hbl]
    try wp_auto
    rw [Htx]
    try wp_auto
    -- the freelist
    unfold dbWR
    icases Hdbw with ⟨Hdb, %Hdw⟩
    have Hdw' := Hdw
    obtain ⟨hAl, hrw, hdata, hps, hfli, w, hw, hwp, hwq, hwh, htx, htb⟩ := Hdw'
    rw [hfli]
    simp only [FLImpl.iface, interface.mkOk]
    try wp_auto
    have Hpgw : w.pages !! uint.nat nv.pgid' = some pg := by rw [hwp]; exact Hpg
    have Hnew := freedOK_hnew W HvOK ρ.fl txid F HF Hdisj.1 _ pg Hpg HFn
    have HidW : W64 ((uint.nat nv.pgid' : Nat) : Int) = nv.pgid' := by unfold uint.nat; word
    icases ownDB_free I W.dbl γd ρ w hw txid htx htb _ pg Hpgw Hnew $$ Hdb
      with ⟨%fls, %hcan, Hfl, Hdbback⟩
    icases (page_header_bytes (W.data +ₗ ((uint.nat nv.pgid' * W.ps : Nat) : Int)) (DFrac.own W.q) pg
      Hl16 Hcar).1 $$ Hpgb with ⟨Hhd, Hrest⟩
    have Hcan' : ρ.fl.canFree txid (pageOf pg).id' (uint.nat (pageOf pg).overflow' + 1) := by
      rw [freex_ov pg]
      have : (pageOf pg).id' = W64 ((uint.nat nv.pgid' : Nat) : Int) := by
        simp only [pageOf]; rw [Hid]
      rw [this]; exact hcan
    rw [Hmtx]
    wp_apply hFree fls ρ.fl txid _ (pageOf pg) (DFrac.own W.q) Hcan' $$ [Hfl Hhd] as ⟨Hfl, Hhd⟩
    · iframe
    try wp_auto
    have Heq : ρ.fl.freePages txid (W64 (pageId pg : Int)) (uint.nat (W32 (pageOverflow pg : Int)) + 1) =
        ρ.fl.freePages txid (W64 ((uint.nat nv.pgid' : Nat) : Int)) (1 + pageOverflow pg) := by
      have := freex_ov pg
      simp only [pageOf] at this
      rw [this, Hid]
    isimp only [Heq] at Hfl
    ihave Hdb := Hdbback $$ Hfl
    ihave Hpgb := (page_header_bytes (W.data +ₗ ((uint.nat nv.pgid' * W.ps : Nat) : Int)) (DFrac.own W.q) pg
      Hl16 Hcar).2 $$ [Hhd Hrest]
    · iframe
    ihave Hpv := Hpvback $$ Hpgb
    ihave HFt := pgToks_insert γ F _ pg HFn $$ [HFt Htok]
    · iframe
    iapply HΦ
    iexists { ρ with fl := ρ.fl.freePages txid (W64 ((uint.nat nv.pgid' : Nat) : Int)) (1 + pageOverflow pg) },
      <[uint.nat nv.pgid' := pg]> F
    rw [Hbl]
    iframe
    iframe #
    ipureintro
    refine ⟨Hlgv, ⟨hAl, hrw, hdata, hps, trivial, w, hw, hwp, hwq, hwh, htx, htb⟩,
      freedOK_free W HvOK ρ.fl txid F HF _ pg Hpg HFn, ⟨_, rfl⟩, fun h => absurd h h0,
      fun _ => ⟨pg, Hpg, rfl, rfl⟩⟩

end proof

end bbolt
end EtcdGrove
end Perennial
