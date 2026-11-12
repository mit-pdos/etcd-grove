/-
**`Commit`'s free of the synced freelist page** (U10m): `tx.db.freelist.Free(txid, p)` with `p`
the mapping's page `f` (the committed synced freelist page): the page's slots carved out of the
writer's `W` (`wSlots_carve`), their cells read against the page cache (`wrSlots_agree`, at the
`Free` call's step) as `slotsOwn`, the page's header read from them for `Free`, then given to the
store (`store_free_fl`), which hands the writer the recorded bytes' token (`fbTok`). The writer
side after it is `w.freeFl f n` (`Commit/FreeFlPure`), of which `wdbOK' true` holds.

Two premises no clause of `wdbOK` gives (reported): the page's header names it (`hid : pageId
(w.wb f) = f`; `flCurOK` has no such clause) and its `allocs` entry is not the writer's txid
(`hal`; `Free`'s `canFree`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.FreeFlPure
public import Proof.go_etcd_io.bbolt.Inv.Bolt
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Free

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The free of the synced freelist page `f`** (see the file header). -/
theorem cm_free_fl (wp_FlFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (v : View) (w : WDb) (f : Nat) (b : Loc) (l : Nat)
    (hok : wdbOK w) (hms : w.ms = some (b, l)) (hf : w.C.flpg = some f)
    (hlen : w.fl.allIds.length < 2 ^ 48)
    (hal : (w.fl.allocs !! W64 (f : Int)).getD 0 ≠ w.wtxid)
    (hid : pageId (w.wb f) = f) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ K.core ∗
        wdbLive K.B K.db K.p K.sp K.t0 tx (wLive v w.C) w }}
      (App (App (ifaceCall w.fli go!"Free") (Val #w.wtxid))
        (Val #(b +ₗ ((f * 4096 : Nat) : Int))))
    {{ RET #(); wdbLive K.B K.db K.p K.sp K.t0 tx (wLive v w.C)
          (w.freeFl f (1 + pageOverflow (w.wb f))) ∗
        fbTok K.B w.C (w.freeFl f (1 + pageOverflow (w.wb f))).fl (wLive v w.C)
          (fbRec (W64 (f : Int)) (1 + pageOverflow (w.wb f)) w.wb) }} := by
  obtain ⟨h16, hf2, hfh, hh51, hrun, hcan, -, -, -⟩ := freeFl_ok w f hok hf hlen
  have hcan := hcan hal
  have hf64 : f < 2 ^ 64 := by omega
  have hfW : (W64 (f : Int)).toNat = f := toNat_W64_of_lt _ hf64
  wp_start as ⟨#Hcore, Hd⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨-, -, -, -, #Hos, -, -, -, -, #Hpi, -⟩
  iunfold wdbLive at Hd
  iunfold wdbCoreG at Hd
  icases Hd with ⟨⟨Hcur, Hgfl, Hgmap, Hout, Hgwv, Hfli, Hopn, Hwa, Hrw, Hfile, Hpath, Hdsz, Hmf,
    Hom, Hfo, Hfd, Hmc, Hmb, Hwc, Hwbs, Hjk⟩, Hflo, Hsp, Hrc⟩
  -- the run's slots out of `W`
  have hsub : ∀ s ∈ List.range' f (1 + pageOverflow (w.wb f)), s ∈ w.W := by
    intro s hs
    rw [List.mem_range'_1] at hs
    have := (hrun (s - f) (by omega)).1
    rwa [show f + (s - f) = s by omega] at this
  have hin : ∀ s ∈ List.range' f (1 + pageOverflow (w.wb f)),
      4096 * (s + 1) ≤ l ∧ 4096 * (s + 1) ≤ w.m.size := by
    intro s hs
    rw [List.mem_range'_1] at hs
    obtain ⟨-, -, -, hm, hz⟩ := hrun (s - f) (by omega)
    rw [show f + (s - f) = s by omega] at hm hz
    have := hm b l hms
    refine ⟨?_, hz⟩
    have := Nat.mul_le_of_le_div 4096 (s + 1) l (by omega)
    omega
  have hlen4 : ∀ s ∈ List.range' f (1 + pageOverflow (w.wb f)),
      4096 * (s + 1) ≤ l ∧ (w.wb s).length = 4096 := by
    intro s hs
    refine ⟨(hin s hs).1, ?_⟩
    rw [List.mem_range'_1] at hs
    have := (hrun (s - f) (by omega)).2.2.1
    rwa [show f + (s - f) = s by omega] at this
  rw [hms]
  icases wSlots_carve b l K.p w.W (List.range' f (1 + pageOverflow (w.wb f))) w.wb w.m.size
    List.nodup_range' hsub hin $$ [Hwc Hwbs] with ⟨HS, Hwc, Hwbs⟩
  · iframe
  have hbm : w.m.maps !! b = some l := by rw [hok.1 b l hms]; simp [GMap.singleton]
  -- the cells' bytes, at the call's step
  iapply wrSlots_agree _ rfl K.p (DFrac.own 1) w.m b l hbm (by simp) w.wb _ _ hlen4 $$ Hos Hom HS
  iintro Hom HS
  -- the page's header
  unfold slotsOwn
  rw [show 1 + pageOverflow (w.wb f) = pageOverflow (w.wb f) + 1 by omega, List.range'_succ]
  icases BigSepL.bigSepL_cons.1 $$ HS with ⟨⟨Hpg, Hos0⟩, HS⟩
  have hpgne : w.wb f ≠ [] := by intro h; rw [h] at h16; simp at h16
  ihave %Hpos := bytesPointsto_pos _ _ _ hpgne $$ Hpg
  icases bytesPointsto_view_read (V := Page) (b +ₗ ((4096 * f : Nat) : Int))
    (DFrac.own (1 : Qp).half) (w.wb f) 0 (b +ₗ ((f * 4096 : Nat) : Int))
    (by rw [Nat.mul_comm]; simp [loc_add_0]) (by omega) Hpos $$ Hpg with ⟨Hhdr, Hclose⟩
  rw [show (decode (((w.wb f).drop 0).take 16) : Page) = pageHdr (w.wb f) from rfl]
  have hhid : (pageHdr (w.wb f)).id' = W64 (f : Int) := by
    apply BitVec.eq_of_toNat_eq; rw [hfW]; exact hid
  have hcan' : w.fl.canFree w.wtxid (pageHdr (w.wb f)).id' (1 + (pageHdr (w.wb f)).overflow'.toNat) := by
    rw [hhid]; exact hcan
  have hov' : (pageHdr (w.wb f)).overflow'.toNat = pageOverflow (w.wb f) := rfl
  generalize hH : pageHdr (w.wb f) = hdr at hhid hcan' hov' ⊢
  iapply wp_fupd
  wp_apply wp_FlFree w.fli w.fl w.wtxid _ hdr (DFrac.own (1 : Qp).half) hcan'
    $$ [Hflo Hhdr] as ⟨Hflo, Hhdr⟩
  · iframe
  ihave Hpg := Hclose $$ Hhdr
  -- the store's step
  imod (store_free_fl K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl (some (b, l)) (wLive v w.C)
    (w.C.txid + 1) (W64 (f : Int)) (1 + pageOverflow (w.wb f)) w.wb rfl rfl hcan (by omega)
    (by rw [hfW]; exact hf) (by simp) (by rw [hfW]; exact hfh)
    (fun j hj => by
      rw [hfW]
      obtain ⟨-, a, c, d, -⟩ := hrun j hj
      exact ⟨a, c, fun b' l' e => d b' l' (hms.trans e)⟩))
    $$ [Hpi Hcur Hgfl Hgmap Hgwv Hpg Hos0 HS] with ⟨Hcur, Hgfl, Hgmap, Hgwv, Htok, -⟩
  · iframe; iframe #
    unfold slotsOwn
    rw [hfW, show 1 + pageOverflow (w.wb f) = pageOverflow (w.wb f) + 1 by omega,
      List.range'_succ]
    iapply BigSepL.bigSepL_cons.2
    iframe
  imodintro
  iapply HΦ
  unfold wdbLive wdbCoreG
  simp only [WDb.freeFl.proj_C, WDb.freeFl.proj_fl, WDb.freeFl.proj_ms, WDb.freeFl.proj_W,
    WDb.freeFl.proj_wb, WDb.freeFl.proj_m, WDb.freeFl.proj_fli, WDb.freeFl.proj_f,
    WDb.freeFl.proj_fd, WDb.freeFl.proj_junk]
  rw [hms]
  iframe
  ihave Hflo : flPgOwn w.fli (w.fl.freePages w.wtxid (W64 (f : Int)) (1 + pageOverflow (w.wb f)))
    $$ [Hflo]
  · rw [← hhid, ← hov']; iexact Hflo
  simp only [WDb.wtxid]
  rw [show pageOverflow (w.wb f) + 1 = 1 + pageOverflow (w.wb f) by omega]
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
