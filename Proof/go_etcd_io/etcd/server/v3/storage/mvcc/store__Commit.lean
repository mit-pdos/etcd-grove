/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/store__Commit.lean` (D22 S-l's sender items,
2026-10-22). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Commit
public import Proof.ReceiptTactics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.mu.Lock()` gives the whole of `s.mu`'s resource, whose share of the fields the writer's
fragment pins at `γ`'s names: `s.b` is the backend of `γ`'s contract (`physOk`), whose
`ForceCommit()` takes the writer's reader token and a write session's token. -/
theorem mvcc.store.Commit.wp_proof : mvcc.store.Commit.spec (GF := GF) (hG := hG) := by
  intro s γ qf o X Y
  wp_start as ⟨#Hs, Hpin, Hrd, Hwt, HX, #Hrq⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HmuP⟩
  -- the write token: the caller's, or from its supply with this step's receipt
  wp_take_receipt as Hrcp
  ihave Hwt : |={⊤}=> mvcc.storeWT (GF := GF) γ $$ [Hwt Hrcp]
  · icases Hwt with (Hwt | #Hsup)
    · imodintro; iexact Hwt
    · iapply Hsup; iexact Hrcp
  imod Hwt
  wp_auto_lc 4
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ 1)) $$ Hlc1 HmuP with HmuP
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.storeReaderC s γ)) $$ Hlc2 Hrd with Hrd
  iunfold mvcc.storeReaderC at Hrd
  iNamedSuffix Hrd "R"
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%c, Hmi, Hwr, Hfs⟩
  -- the caller's share pins the fields' share at `γ`'s names
  icases mvcc.fieldShare_pin s γ _ _ o $$ [$Hpin $Hfs] with ⟨Hpin, Hfs⟩
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  ihave #Hph' := Hph
  iunfold mvcc.physOk at Hph'
  iNamed Hph'
  -- a slot of the index's readers' pool: a reader token of the backend for `ForceCommit`
  -- (`s.mu` held exclusively: its deposit ghost whole) a reader's share of it, `1 = rfrac + rest`
  have h1 : (1 : Qp) = sync.rfrac + sync.invFrac 1 := by
    rw [← sync.invFrac_0]; exact sync.invFrac_S 0 (by have := sync.actualMaxReaders_pos; omega)
  have hf := (ghostVar_fractional (GF := GF) γ.wr ()).fractional sync.rfrac (sync.invFrac 1)
  rw [← h1] at hf
  icases hf.1 $$ Hwr with ⟨Hwr, HwrR⟩
  icases (mvcc.wDep_halves γ).1 $$ Hwr with ⟨Hwr, Hwr2⟩
  imod mvcc.readerPool_checkout γ _ o $$ Hlc3 Hpool Hpin HtkR Hwr2 with ⟨Hslot, Htko, Hpin⟩
  iunfold mvcc.idxSlot at Hslot
  icases Hslot with ⟨HtiR, HrtR⟩
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, -, -, -, #HForce, -⟩
  (try wp_auto)
  rw [Hbi]
  (try wp_auto)
  -- `s.b.ForceCommit()`
  wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
  iapply HForce $$ %X %Y [HrtR Hwt HX] [-]
  · iframe HrtR Hwt HX
    iframe #
  inext
  iintro ⟨HrtR, HY⟩
  imod mvcc.readerPool_checkin γ _ o $$ Hlc4 Hpool Hpin [HtiR HrtR] Htko with ⟨HtkR, Hwr2, Hpin⟩
  · iunfold mvcc.idxSlot; iframe HtiR HrtR
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmi Hwr Hwr2 HwrR Hcur Hfb Hfidx Hfsch Hfstop Hfrst]
  · inext
    iunfold mvcc.muInv
    iexists c
    iframe Hmi
    isplitl [Hwr Hwr2 HwrR]
    · iapply hf.2
      iframe HwrR
      iapply (mvcc.wDep_halves γ).2; iframe Hwr Hwr2
    iapply mvcc.fieldShare_of_at
    iunfold mvcc.fieldShareAt
    iframe Hcur Hfrst Hph
    iunfold mvcc.storeFields
    simp only [named]
    rw [Hbi]
    iframe Hfb Hfidx Hfsch Hfstop
  (try wp_auto)
  iapply HΦ
  iframe Hpin HY
  iunfold mvcc.storeReaderC
  simp only [named]
  iframe HmuR HrevMuR HtkR

end proof

end EtcdGrove
end Perennial
