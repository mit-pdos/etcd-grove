/-
**`KV.Commit` and `KV.HashStorage` at both store types** (2026-11-06). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

* `Commit`: the store's `Commit` (`store.Commit.spec`: under `s.mu`, the backend's `ForceCommit`
  with a reader token of the backend from the readers' pool) over the backend share's current names
  (`mvccBackend`'s `curAt`), a reader from the handle (the plain handle's supply, `rdSupply_lendL`;
  the watchable handle's pool, `watchReader_borrow`), the write token from the share's supply, the
  commit request: the contract's `storageReq` is the backend's `commitReq`, one of `storeReq`'s
  disjuncts with the share's `isBackend`. The watchable store's `Commit` is its inner store's
  (promoted).
* `HashStorage`: the store's `hashes` field (`isStore`'s), whose `Store` meets its spec
  (`hashStorage.Store.spec` at `hashStorageOk`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WatchTxnApi
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Commit
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage__Store

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The contract's commit request is the store's at the share's names. -/
private theorem storeReq_of_storage (γ : StoreNames) (p : PhysNames) (d : KBReal) (hpk : p.kb = some d)
    (Pk X Y : IProp GF) :
    □ backend.isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ storageReq (d : MvccStorage) Pk X Y ⊢
      storeReq (γ.withPhys p) X Y := by
  iintro ⟨#Hbk, Hrq⟩
  unfold storeReq kbReq
  rw [StoreNames.withPhys_kb, hpk]
  iunfold bkReq
  iright
  iexists (lateW d.gx), Pk
  iframe Hbk
  iunfold storageReq at Hrq
  iexact Hrq

/-- **`KV.Commit.contract` at `*store`.** -/
theorem store.Commit.wp_api (hC : mvcc.store.Commit.spec (GF := GF) (hG := hG)) :
    store.Commit.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) q B Pk X Y
  iintro %Φ ⟨#Hpkg, Hmv, Htok, HB, HX, Hrq⟩ HΦ
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  rotate_left 1
  · iunfold isMvccWatchable at Hmv
    icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, -⟩
    exfalso
    obtain ⟨Hk, -⟩ := Hk
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccPlain at Hmv
  icases Hmv with ⟨%s', %Hk, #Hs, #Hloc, -, #Hsup, -⟩
  have hs : s = s' := mkOk_loc_inj _ Hk
  subst hs
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p, %o, %d, Hcur, %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
  obtain ⟨hpk, hcm, hdB⟩ := Hd
  subst hdB
  iapply wp_fupd
  imod mvcc.rdSupply_lendL s γ $$ [$Hsup $Htok] with ⟨Hrd, Hback⟩
  ihave Hrd : ▷ storeReaderC (GF := GF) s (γ.withPhys p) $$ [Hrd]
  · rw [storeReaderC_withPhys]; iexact Hrd
  ihave #Hreq := storeReq_of_storage γ p d hpk Pk X Y $$ [$Hbk $Hrq]
  iapply (hC s (γ.withPhys p) _ o X Y) $$ [Hcur Hrd HX] [HΦ Hback HF]
  · rw [isStore_withPhys]
    iframe Hpkg Hs Hcur Hrd HX Hreq
    iright; iexact Hwts
  inext
  iintro ⟨Hcur, Hrd, HY⟩
  ihave Hrd : storeReaderC (GF := GF) s γ $$ [Hrd]
  · rw [← storeReaderC_withPhys s γ p]; iexact Hrd
  iunfold tokBack at Hback
  imod Hback $$ Hrd with Htok
  imodintro
  iapply HΦ
  iframe Htok HY
  iunfold mvccBackend
  iframe HF
  iexists p, o, d
  iframe Hcur Hbk Hrg Hhp Hwts
  ipureintro; exact ⟨⟨hpk, hcm, rfl⟩, Hlp⟩

/-- **`KV.Commit.contract` at `*watchableStore`**: its inner store's (promoted). -/
theorem watchableStore.Commit.wp_api (hC : mvcc.store.Commit.spec (GF := GF) (hG := hG)) :
    watchableStore.Commit.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) q B Pk X Y
  wp_start as ⟨Hmv, Htok, HB, HX, Hrq⟩
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  · iunfold isMvccPlain at Hmv
    icases Hmv with ⟨%s', %Hk, -⟩
    exfalso
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccWatchable at Hmv
  icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, #Hws, -, #Hrp, #Hloc, -⟩
  obtain ⟨Hk, hγ⟩ := Hk
  rw [interface_mkOk_inj] at Hk
  have hs : s = s' := go.intoVal_inj Hk.2
  subst hs hγ
  ihave #Hws' := Hws
  iunfold isWatchableStore at Hws'
  icases Hws' with ⟨%vc, %stc, %rv, %γv, Hws'⟩
  iNamed Hws'
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p, %o, %d, Hcur, %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
  obtain ⟨hpk, hcm, hdB⟩ := Hd
  subst hdB
  wp_auto_lc 1
  iapply fupd_wp
  imod watchReader_borrow s st γw γp $$ [$Hlc1 $Hrp $Htok] with ⟨Hrd, Hback⟩
  imodintro
  iapply wp_fupd
  ihave Hrd : ▷ storeReaderC (GF := GF) st (γw.st.withPhys p) $$ [Hrd]
  · rw [storeReaderC_withPhys]; inext; iexact Hrd
  ihave #Hreq := storeReq_of_storage γw.st p d hpk Pk X Y $$ [$Hbk $Hrq]
  wp_apply (hC st (γw.st.withPhys p) _ o X Y) $$ [Hcur Hrd HX] as ⟨Hcur, Hrd, HY⟩
  · rw [isStore_withPhys]
    iframe Hs Hcur Hrd HX Hreq
    iright; iexact Hwts
  ihave Hrd : storeReaderC (GF := GF) st γw.st $$ [Hrd]
  · rw [← storeReaderC_withPhys st γw.st p]; iexact Hrd
  iunfold tokBack at Hback
  imod Hback $$ Hrd with Htok
  imodintro
  iapply HΦ
  iframe Htok HY
  iunfold mvccBackend
  iframe HF
  iexists p, o, d
  iframe Hcur Hbk Hrg Hhp Hwts
  ipureintro; exact ⟨⟨hpk, hcm, rfl⟩, Hlp⟩

/-- The store's `hashes` meets `hashStoreOk`. -/
theorem hashStoreOk_of (hHS : mvcc.hashStorage.Store.spec (GF := GF) (hG := hG)) (shs : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.hashStorageOk shs ⊢
      hashStoreOk (interface.mkOk (go.GoType.PointerType hashStorage.ty) #shs : GoInterface) := by
  iintro ⟨#Hpkg, #Hok⟩
  iunfold hashStoreOk
  iintro !> %ty %v %kh %Heq %Φ !> - HΦ
  rw [interface_mkOk_inj] at Heq
  obtain ⟨rfl, hv⟩ := Heq
  have hv' : v = #shs := hv.symm
  subst hv'
  wp_apply (hHS shs kh) $$ [$Hpkg $Hok]
  iapply HΦ; itrivial

/-- **`KV.HashStorage.contract` at `*store`.** -/
theorem store.HashStorage.wp_api (hHS : mvcc.hashStorage.Store.spec (GF := GF) (hG := hG)) :
    store.HashStorage.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames)
  wp_start as Hmv
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  rotate_left 1
  · iunfold isMvccWatchable at Hmv
    icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, -⟩
    exfalso
    obtain ⟨Hk, -⟩ := Hk
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccPlain at Hmv
  icases Hmv with ⟨%s', %Hk, #Hs, -⟩
  have hs : s = s' := mkOk_loc_inj _ Hk
  subst hs
  iunfold isStore at Hs
  iNamed Hs
  wp_auto
  iapply HΦ
  iapply hashStoreOk_of hHS shs $$ [$HhsOk]
  iPkgInit

/-- **`KV.HashStorage.contract` at `*watchableStore`**: its inner store's (promoted). -/
theorem watchableStore.HashStorage.wp_api (hHS : mvcc.hashStorage.Store.spec (GF := GF) (hG := hG)) :
    watchableStore.HashStorage.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames)
  wp_start as Hmv
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  · iunfold isMvccPlain at Hmv
    icases Hmv with ⟨%s', %Hk, -⟩
    exfalso
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccWatchable at Hmv
  icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, #Hws, -⟩
  obtain ⟨Hk, hγ⟩ := Hk
  rw [interface_mkOk_inj] at Hk
  have hs : s = s' := go.intoVal_inj Hk.2
  subst hs
  iunfold isWatchableStore at Hws
  icases Hws with ⟨%vc, %stc, %rv, %γv, Hws⟩
  iNamed Hws
  iunfold isStore at Hs
  iNamed Hs
  wp_auto
  wp_method_call; wp_call
  (try wp_auto)
  iapply HΦ
  iapply hashStoreOk_of hHS shs $$ [$HhsOk]
  iPkgInit

end proof

end api
end mvcc
end EtcdGrove
end Perennial
