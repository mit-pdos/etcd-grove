module
public import Spec.go_etcd_io.bbolt.Tx__commitFreelist
public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Spec.go_etcd_io.bbolt.Tx__rollback_w
public import Spec.go_etcd_io.bbolt.Tx__rollback_l
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetFreelist
public import Proof.go_etcd_io.bbolt.DBAcc

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

/-- What a dereference keeps of the transaction. -/
theorem cf_deref_facts (T T0 : WTx) (rl : Loc) (h : T0 = T ∨ derefRel T T0) :
    T0.t.writable' = T.t.writable' ∧ T0.t.db' = T.t.db' ∧ T0.mv = T.mv ∧
      ((T.bs !! rl).isSome → (T0.bs !! rl).isSome) := by
  rcases h with rfl | ⟨ht, hmv, -, -, hdom, -⟩
  · exact ⟨rfl, rfl, rfl, id⟩
  · exact ⟨by rw [ht], by rw [ht], hmv, (hdom rl).1⟩

theorem Tx.commitFreelist.wp_wproof
    (hAlloc : Tx.allocate.wspec (GF := GF) (hG := hG))
    (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hSetFl : Meta.SetFreelist.spec (GF := GF) (hG := hG))
    (hRb : Tx.rollback.wspec (GF := GF) (hG := hG))
    (hRbl : Tx.rollback.lspec (GF := GF) (hG := hG)) :
    Tx.commitFreelist.wspec (GF := GF) (hG := hG) := by
  intro I γ W txl T ρ hEW hWr hRbS hRlS hFC hPC hn Hpg Hhwm Hready Hdb Hcar Htxs Hwr
  wp_start as ⟨HR, HG, Hv⟩
  ihave #Hflpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist) $$ []
  · iPkgInit
  ihave #Hcom : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common) $$ []
  · iPkgInit
  isimp only [dbWR] at HR
  icases HR with ⟨Hown, %Hf⟩
  have Hf' := Hf
  obtain ⟨HAS, Hrw, Hdata, Hps, Hfli, w, Hw, Hwp, Hwq, Hwh, Htxw, Htxb⟩ := Hf'
  icases persistent_entails_left (ownDB_dbOK I W.dbl γ ρ) $$ Hown with ⟨Hown, %Hdbok⟩
  obtain ⟨v0, v1, Hdbok⟩ := Hdbok
  have Hps80 : 80 ≤ W.ps := Hps ▸ Hdbok.1
  have Hps32 : W.ps < 2 ^ 32 := Hps ▸ Hdbok.2.1
  icases ownDB_flAcc I W.dbl γ ρ $$ Hown with ⟨%fls, Hfl, Hback⟩
  unfold ownWriteTxG
  icases HG with ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩
  isimp only [TxW_rest_root] at Hrest
  icases Hrest with ⟨Hwritable, Hmanaged, Hdbf, Hmetaf, Hpages, Hstats, Hch, Hwf, %Htxn⟩
  isimp only [wView] at Hv
  icases Hv with ⟨Hdatav, #Hps', #Hlg, Hfliv, #Hdl, %Hlgv, Hpv⟩
  wp_auto
  rw [Hdb]
  try wp_auto
  rw [Hfli]
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  wp_apply hEW fls ρ.fl $$ [Hfl] as Hfl
  · iframe
  try wp_auto
  obtain ⟨Hcu, Hc0, Hc1, Hc2, Hclt⟩ := flAllocCount_bounds ρ.fl.allIds.length W.ps hn Hps80 Hps32
  rw [show (W64 (16 + 8 * ((flCells ρ.fl.allIds.length : Nat) : Int)) : w64) =
    W64 ((16 + 8 * flCells ρ.fl.allIds.length : Nat) : Int) by push_cast; rfl,
    flAllocCount_eq _ _ hn Hps80 Hps32]
  ihave Hown := Hback $$ Hfl
  ihave HR : dbWR I γ W txl T.mv.txid' ρ $$ [Hown]
  · unfold dbWR; iframe; ipureintro; exact Hf
  ihave HG : ownWriteTxG W txl T $$ [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf Hm Hpm Hbufs Hbs]
  · unfold ownWriteTxG TxW_rest_root; rw [Hdb]; iframe; ipureintro; exact Htxn
  ihave Hv : wView W $$ [Hdatav Hfliv Hpv]
  · unfold wView; rw [Hfli]; try simp only [FLImpl.iface, interface.mkOk]
    iframe; iframe #; ipureintro; exact Hlgv
  wp_apply hAlloc I γ W txl T ρ (flAllocCount ρ.fl.allIds.length W.ps) Hc0 Hc1 Hc2 Hpg Hhwm Hready
    Hdb Hcar Htxs (by omega) $$ [HR HG Hv] as %p %err Hpost
  · iframe
  try wp_auto
  icases Hpost with (⟨%ρ', %data', %T0, %T', HR, HG, Hv, %Hres⟩ | ⟨%Herr, %T0, %Hrel, Hlost, HG⟩)
  · have Hres' := Hres
    obtain ⟨⟨Hd0, Hr⟩, HaD⟩ := Hres'
    rcases Hr with ⟨Herr, HT'⟩ | ⟨Herr, id, st, hwm', Hid2, Hpgle, Hidn, Hhw48, Hnc, Hun, HT'⟩
    · -- an error, the database unchanged: the writer rolled back
      obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
        cases err with
        | nil => exact absurd rfl Herr
        | ok e => exact ⟨e, rfl⟩
      have Hρ := HaD.1 Herr
      subst Hρ HT'
      try wp_auto
      obtain ⟨hwr0, hdb0, hmv0, hroot0⟩ := cf_deref_facts T T' (structFieldRef Tx go!"root" txl)
        (Hd0.imp (fun h => h.1) (fun h => h.1))
      wp_apply hRb I γ { W with data := data' } txl T.mv.txid' ρ' T' hRbS hRlS hFC hPC hEW
        (by rw [hwr0]; exact Hwr) (by rw [hdb0]; exact Hdb) (hroot0 Hready.1) (by rw [hmv0])
        $$ [HR HG Hv] as ⟨%w', %free', %t, %Hwf', Hown, Htx, %Ht⟩
      · iframe
      try wp_auto
      iapply HΦ
      iright; ileft
      isplitr
      · ipureintro; nofun
      iexists w', free', t
      iframe
      ipureintro; exact ⟨Hwf', Ht⟩
    · -- the page allocated: `Write` makes it the freelist page
      subst Herr
      try wp_auto
      obtain ⟨wa, ida, Hwa, Haok⟩ := HaD.2 rfl
      have Hle := allocOK_allIds_le _ _ _ _ _ _ _ _ Haok
      have Hkle := flCells_mono _ _ Hle
      obtain ⟨hwr0, hdb0, hmv0, hroot0⟩ := cf_deref_facts T T0 (structFieldRef Tx go!"root" txl)
        (Hd0.imp (fun h => h.1) (fun h => h.1))
      generalize Hcnt : flAllocCount ρ.fl.allIds.length W.ps = cnt at *
      generalize Hk : flCells ρ'.fl.allIds.length = k at *
      have Hcnt0 : 0 < uint.nat cnt := by have := Hc0; unfold uint.nat; word
      have Hcnt32 : uint.nat cnt ≤ 2 ^ 32 := by
        have := Hc1; unfold uint.nat; word
      have Hk60 : k < 2 ^ 60 := by
        have := flCells_le ρ.fl.allIds.length; omega
      subst HT'
      -- the database's freelist
      isimp only [dbWR] at HR
      icases HR with ⟨Hown, %Hf2⟩
      icases ownDB_flAcc I _ γ ρ' $$ Hown with ⟨%fls', Hfl, Hback⟩
      -- the transaction's page
      isimp only [ownWriteTxG] at HG
      icases HG with ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩
      isimp only [TxW_rest_root] at Hrest
      icases Hrest with ⟨Hwritable, Hmanaged, Hdbf, Hmetaf, Hpages, Hstats, Hch, Hwf, %Htxn'⟩
      isimp only [wView] at Hv
      icases Hv with ⟨Hdatav, #Hps2, #Hlg2, Hfliv, #Hdl2, %Hlgv2, Hpv⟩
      icases bufs_update (GF := GF) _ _ id p (by simp only [allocT]; exact GMap.lookup_insert _ _ _)
        $$ Hbufs with ⟨⟨%b, %Hb, Hpb⟩, Hbufs⟩
      have Hbeq : b = freshPage id (uint.nat cnt) W.ps := by
        simp only [allocT] at Hb; rw [GMap.lookup_insert] at Hb; exact (Option.some.inj Hb).symm
      subst Hbeq
      have Hpne : freshPage id (uint.nat cnt) W.ps ≠ [] := by
        intro h; have := congrArg List.length h; simp [freshPage, leBytes_length'] at this
      ihave %Hpcar := bytesPointsto_car p _ _ Hpne $$ Hpb
      have Hk16 : 16 + 8 * k ≤ uint.nat cnt * W.ps := by omega
      icases fresh_fl_split (GF := GF) p id (uint.nat cnt) W.ps k Hpcar Hcnt0 Hcnt32 Hk16 Hk60 $$ Hpb
        with ⟨Hhd, Hsl, Hz⟩
      ihave Hsl : slice.mk (p +ₗ 16) (W64 ((List.replicate k (W64 0)).length : Int))
          (W64 ((List.replicate k (W64 0)).length : Int)) ↦* List.replicate k (W64 0) $$ [Hsl]
      · rw [List.length_replicate]; iexact Hsl
      have HdbT : (allocT T0 st hwm' id p (freshPage id (uint.nat cnt) W.ps)).t.db' = W.dbl := by
        simp only [allocT]; rw [hdb0, Hdb]
      rw [HdbT]
      try wp_auto
      try simp only
      try rw [Hfli]
      try simp only [FLImpl.iface, interface.mkOk]
      try wp_auto
      wp_apply hWr fls' ρ'.fl p _ (List.replicate k (W64 0)) Hpcar (by rw [List.length_replicate, Hk])
        $$ [Hfl Hhd Hsl] as %out ⟨%Hout, Hfl, Hhd, Hsl⟩
      · iframe
      try wp_auto
      wp_apply hId p _ (DFrac.own 1) $$ [Hhd] as Hhd
      · iframe
      try wp_auto
      wp_apply hSetFl _ _ _ $$ [Hm] as Hm
      · simp only [allocT]; iframe
      try wp_auto
      -- the page's bytes back into the page cache
      have Hcl : (flCellsOf ρ'.fl.allIds.length out).length = k := by
        rw [← Hk]; exact flCellsOf_length _ _ Hout.2.length_eq
      ihave Hsl : slice.mk (p +ₗ 16) (W64 (k : Int)) (W64 (k : Int)) ↦*
          flCellsOf ρ'.fl.allIds.length out $$ [Hsl]
      · unfold flCellsOf
        rw [show (k : Int) = ((List.replicate k (W64 0)).length : Int) by simp]
        iexact Hsl
      ihave Hpg := fl_written_join (GF := GF) p _ (flCellsOf ρ'.fl.allIds.length out) k _ Hpcar Hcl
        (by omega) $$ [Hhd Hsl Hz]
      · iframe
      ihave Hbufs := Hbufs $$ Hpg
      ihave Hown := Hback $$ Hfl
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists ρ', data', T0, (allocT T0 st hwm' id p (freshPage id (uint.nat cnt) W.ps)), id, p, out
      isplitl [Hown]
      · unfold dbWR; iframe; ipureintro
        obtain ⟨a1, a2, a3, a4, -, a6⟩ := Hf2
        exact ⟨a1, a2, a3, a4, rfl, a6⟩
      isplitl [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf Hm Hpm Hbufs Hbs]
      · try unfold ownWriteTxG
        try unfold TxW_rest_root
        unfold flWritten
        rw [Hk]
        simp only [allocT]
        try rw [hdb0, Hdb]
        iframe
        ipureintro; exact Htxn'
      isplitl [Hdatav Hfliv Hpv]
      · unfold wView; iframe; iframe #; ipureintro; exact Hlgv2
      ipureintro
      exact ⟨Hres.1, Hres.2, ⟨st, hwm', rfl⟩, Hout⟩
  · -- the remap failed after the dereference: the database lost, the writer rolled back
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok e => exact ⟨e, rfl⟩
    try wp_auto
    obtain ⟨hwr0, hdb0, hmv0, hroot0⟩ := cf_deref_facts T T0 (structFieldRef Tx go!"root" txl)
      (Or.inr Hrel.1)
    wp_apply hRbl I W txl T.mv.txid' ρ.fl T0 hRbS hFC hPC hEW (by rw [hwr0]; exact Hwr)
      (by rw [hdb0]; exact Hdb) (hroot0 Hready.1) (by rw [hmv0]) $$ [Hlost HG] as ⟨%t, Htx, %Ht⟩
    · iframe
    try wp_auto
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; nofun
    iexists t
    iframe
    ipureintro; exact Ht

end proof

end bbolt
end EtcdGrove
end Perennial
