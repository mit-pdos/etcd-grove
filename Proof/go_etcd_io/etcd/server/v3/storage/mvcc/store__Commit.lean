/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/store__Commit.lean` (D22 S-l's sender items,
2026-10-22). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Commit
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
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
  intro s γ X Y
  wp_start as ⟨#Hs, Hfr, Hro, Hwt, HX, #Hrq⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HmuP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ 1)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%c, Hmi, Hwr, Hfs⟩
  -- the writer's fragment pins the fields' share at `γ`'s names
  iunfold mvcc.writerFrag at Hfr
  icases Hfr with ⟨⟨%o, Hpin⟩, %Hoffw⟩
  icases mvcc.fieldShare_pin s γ _ _ o $$ [$Hpin $Hfs] with ⟨Hpin, Hfs⟩
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  ihave #Hph' := Hph
  iunfold mvcc.physOk at Hph'
  iNamed Hph'
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, -, -, -, #HForce, -⟩
  (try wp_auto)
  rw [Hbi]
  (try wp_auto)
  -- `s.b.ForceCommit()`
  wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
  iunfold mvcc.writerOwn at Hro
  icases Hro with ⟨Hro, Htkr⟩
  iapply HForce $$ %X %Y [Hro Hwt HX] [-]
  · iframe Hro Hwt HX
    iframe #
  inext
  iintro ⟨Hro, HY⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmi Hwr Hcur Hfb Hfidx Hfsch Hfstop Hfrst]
  · inext
    iunfold mvcc.muInv
    iexists c
    iframe Hmi Hwr
    iapply mvcc.fieldShare_of_at
    iunfold mvcc.fieldShareAt
    iframe Hcur Hfrst Hph
    iunfold mvcc.storeFields
    simp only [named]
    rw [Hbi]
    iframe Hfb Hfidx Hfsch Hfstop
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.writerOwn
  iframe Hro Htkr HY
  iunfold mvcc.writerFrag
  iframe %Hoffw
  iexists o
  iexact Hpin

/-- **A deposit out of `s.mu`'s whole writer's ghost** (an exclusive holder's): the readers' pool takes
one for a checked-out slot. -/
theorem mvcc.wr_dep (γ : mvcc.StoreNames) :
    ghostVar (GF := GF) γ.wr 1 () ⊢ mvcc.wDep γ ∗ (mvcc.wDep γ -∗ ghostVar γ.wr 1 ()) := by
  have h1 : (1 : Qp) = sync.rfrac + sync.invFrac 1 := by
    rw [← sync.invFrac_0]
    exact sync.invFrac_S 0 (by have := sync.actualMaxReaders_ge_2; omega)
  rw [h1]
  iintro H
  icases ghostVar_split γ.wr () sync.rfrac (sync.invFrac 1) $$ H with ⟨Hr, Hi⟩
  icases (mvcc.wDep_halves γ).1 $$ Hr with ⟨Hd1, Hd2⟩
  iframe Hd1
  iintro Hd1
  ihave Hr : ghostVar (GF := GF) γ.wr sync.rfrac () $$ [Hd1 Hd2]
  · iapply (mvcc.wDep_halves γ).2; iframe Hd1 Hd2
  iapply (ghostVar_fractional (GF := GF) γ.wr ()).fractional sync.rfrac (sync.invFrac 1) |>.2
  iframe Hr Hi

/-- **The candidate `Commit`** (`specC`): `spec`'s in the abstract mode, without the writer's
fragment and resources: the fields pinned by the store's pin (`isMvccI`), the write-back token paid
by the first step's receipt, and the backend's reader token checked out of the store's readers' pool
for the duration of `ForceCommit` (with the reader borrowed from the API's pool for the thread token,
and a deposit of `s.mu`'s writer's ghost, which the exclusive lock holds whole). -/
theorem mvcc.store.Commit.wp_proofC : mvcc.store.Commit.specC (GF := GF) (hG := hG) := by
  intro s γ BP Pk b X Y
  iintro %Φ ⟨#Hpkg, #Hmv, Htt, #Hbe, HX, #Hrq⟩ HΦ
  ihave #Hs1 : mvcc.isMvccI s γ $$ []
  · iunfold mvcc.isMvcc at Hmv; iexact Hmv
  ihave #Hs2 := Hs1
  iunfold mvcc.isMvccI at Hs2
  icases Hs2 with ⟨#Hs, %Hf, ⟨%o, #Hpin⟩, -, -, #Hwb, -⟩
  obtain ⟨habs, -, ⟨d, hkb⟩, -, -⟩ := Hf
  -- the client's request, the store's
  ihave #Hrq' : mvcc.storeReq γ.st X Y $$ []
  · iunfold mvcc.mvccBackendIs at Hbe
    iunfold mvcc.mvccBackendIsI at Hbe
    icases Hbe with ⟨%d', %W, %Hd, #Hb, -⟩
    obtain ⟨hkb', hP, hbe⟩ := Hd
    rw [hkb] at hkb'
    cases hkb'
    have hB : mvcc.mvccBackend γ = d.γB := by unfold mvcc.mvccBackend; rw [hkb]
    unfold mvcc.storeReq mvcc.kbReq
    rw [hkb]
    iunfold mvcc.bkReq
    iright
    iexists W, Pk
    subst hP hbe
    iframe Hb
    rw [← hB]
    iexact Hrq
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call; unfold store.Commit.impl; wp_call
  wp_apply wp_with_defer as %defer defer
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HmuP⟩
  -- the deferred unlock's resolution step: its receipt (the write-back token)
  wp_take_receipt as Hrw
  imod Hwb $$ Hrw with Hwt
  wp_auto_lc 4
  imod mvcc.mvccBorrow s γ $$ [$Hlc4 $Hs1 $Htt] with ⟨Hrd, Hloan⟩
  iunfold mvcc.storeReaderC at Hrd
  icases Hrd with ⟨HmuR, HrevMuR, Htk⟩
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ.st 1)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%c, Hmi, Hwr, Hfs⟩
  icases mvcc.fieldShare_pin s γ.st _ _ o $$ [$Hpin $Hfs] with ⟨-, Hfs⟩
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  ihave #Hph' := Hph
  iunfold mvcc.physOk at Hph'
  iNamed Hph'
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, -, -, -, #HForce, -⟩
  (try wp_auto)
  rw [Hbi]
  (try wp_auto)
  -- the backend's reader token, checked out of the store's readers' pool
  icases mvcc.wr_dep γ.st $$ Hwr with ⟨Hdep, Hwr⟩
  imod mvcc.readerPool_checkout γ.st DFrac.discard o $$ Hlc2 Hpool Hpin Htk Hdep with ⟨Hslot, Htko, -⟩
  iunfold mvcc.idxSlot at Hslot
  icases Hslot with ⟨Hidx, Hrt⟩
  -- `s.b.ForceCommit()`
  wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
  iapply HForce $$ %X %Y [Hrt Hwt HX] [-]
  · iframe Hrt Hwt HX
    iframe #
  inext
  iintro ⟨Hrt, HY⟩
  imod mvcc.readerPool_checkin γ.st DFrac.discard o $$ Hlc3 Hpool Hpin [Hidx Hrt] Htko
    with ⟨Htk, Hdep, -⟩
  · iunfold mvcc.idxSlot; iframe Hidx Hrt
  ihave Hwr := Hwr $$ Hdep
  (try wp_auto)
  iapply wp_fupd
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmi Hwr Hcur Hfb Hfidx Hfsch Hfstop Hfrst]
  · inext
    iunfold mvcc.muInv
    iexists c
    iframe Hmi Hwr
    iapply mvcc.fieldShare_of_at
    iunfold mvcc.fieldShareAt
    iframe Hcur Hfrst Hph
    iunfold mvcc.storeFields
    simp only [named]
    rw [Hbi]
    iframe Hfb Hfidx Hfsch Hfstop
  (try wp_auto)
  imod mvcc.mvccGiveBack s γ $$ [$Hs1 $Hloan HmuR HrevMuR Htk] with Htt
  · iunfold mvcc.storeReaderC; iframe HmuR HrevMuR Htk
  imodintro
  (try wp_auto)
  iapply HΦ
  iframe Htt HY

end proof

end EtcdGrove
end Perennial
