/-
**`KV.Close.contract` at both store types** (track A, 2026-11-06). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

* `store.Close.wp_api`: a plain store's `Close` from `store.Close.spec` (the trust boundary): the
  open token at the store's location and current names gives the restorable compaction right, the
  store's right to close in compaction mode (`storeCloserM_on`, by `openRest`'s mode).
* `watchableStore.Close.wp_api`: a watchable store's, as `watchableStore.Close.wp_proof` (its stop
  channel closed, the loops waited for, the inner store closed), with the watchable store's own closer
  from the open token's `openRest` (found through the inner store's read view, which points at the
  receiver) and the inner store's right as the plain store's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Close

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- The open token at the store `s` (its location's): the restorable right at its current names, in
compaction mode, and the rest of `openRest`. -/
private theorem mvccOpen_at (γ : mvcc.StoreNames) (s : Loc) :
    api.locIs γ.api s ∗ mvccOpen (GF := GF) γ ⊢
      ∃ (p : PhysNames) (c : Int), compactRightR s (γ.withPhys p) c ∗
        ⌜kbCmpM (γ.withPhys p).kb⌝ ∗
        (if γ.watchQ then iprop(∃ (w rv stc : Loc),
          s.[store, go!"ReadView"] ↦□
            (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
          rv.[readView, go!"kv"] ↦□
            (interface.mkOk (go.GoType.PointerType watchableStore.ty) #w : GoInterface) ∗
          w.[watchableStore, go!"stopc"] ↦□ stc ∗ stopCloser stc ∗ wsWaiter w)
        else iprop(True)) := by
  iintro ⟨#Hloc, Hopen⟩
  iunfold mvccOpen at Hopen
  icases Hopen with ⟨%s2, %p, %c, #Hloc2, Hright, -, -, -, -, Hor, -⟩
  ihave %Hss := api.locIs_agree γ.api s s2 $$ [Hloc Hloc2]
  · iframe Hloc Hloc2
  cases Hss
  iunfold openRest at Hor
  icases Hor with ⟨%hcm, Hw⟩
  iexists p, c
  iframe Hright Hw
  ipureintro; simp only [StoreNames.withPhys_kb]; exact hcm

/-- **`KV.Close.contract` at `*store`.** -/
theorem store.Close.wp_api (hClose : mvcc.store.Close.spec (GF := GF) (hG := hG)) :
    store.Close.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames)
  iintro %Φ ⟨#Hpkg, Hmv, Hopen⟩ HΦ
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
  icases Hmv with ⟨%s', %Hk, #Hs, #Hloc, -⟩
  have hs : s = s' := mkOk_loc_inj _ Hk
  subst hs
  icases mvccOpen_at γ s $$ [Hloc Hopen] with ⟨%p, %c, Hright, %hcm, -⟩
  · iframe Hloc Hopen
  wp_apply (hClose s (γ.withPhys p) c) $$ [Hright]
  · rw [isStore_withPhys]
    iframe Hs
    iapply (storeCloserM_on s _ c hcm).2
    iexact Hright
  iapply HΦ; itrivial

/-- **`KV.Close.contract` at `*watchableStore`.** -/
theorem watchableStore.Close.wp_api (hClose : mvcc.store.Close.spec (GF := GF) (hG := hG)) :
    watchableStore.Close.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames)
  wp_start as ⟨Hmv, Hopen⟩
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  · iunfold isMvccPlain at Hmv
    icases Hmv with ⟨%s', %Hk, -⟩
    exfalso
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccWatchable at Hmv
  icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, #Hws, -, -, #Hloc, -⟩
  obtain ⟨Hk, hγ⟩ := Hk
  subst hγ
  rw [interface_mkOk_inj] at Hk
  have hs : s = s' := go.intoVal_inj Hk.2
  subst hs
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isWatchableStore at Hws
  iNamed Hws
  icases mvccOpen_at γw.st st $$ [Hloc Hopen] with ⟨%p, %c, Hright, %hcm, Hw⟩
  · iframe Hloc Hopen
  rw [Hwq]
  simp only [↓reduceIte]
  icases Hw with ⟨%w, %rv', %stc', #Hrv', #Hkv', #Hstc', Hstop, Hwait⟩
  icombine Hrv Hrv' gives %Hrv1
  have hrv : rv = rv' := mkOk_loc_inj _ Hrv1
  subst hrv
  icombine Hrvkv Hkv' gives %Hkv1
  have hw : s = w := mkOk_loc_inj _ Hkv1
  subst hw
  icombine Hstopc Hstc' gives %Hst1
  subst Hst1
  iunfold stopCloser at Hstop
  icases Hstop with ⟨%γc, Hstop⟩
  iunfold wsWaiter at Hwait
  icases Hwait with ⟨%γwg, %γd, #HisWg, #Hinv, Hwt⟩
  wp_auto
  wp_apply wp_broadcast_chan_close stc γc iprop(True) $$ [$Hstop] as -
  · imodintro; itrivial
  (try wp_auto)
  iapply fupd_wp
  imod fupd_mask_subseteq (E2 := ↑wsWgWGN) CoPset.subseteq_top with Hmask
  imod sync.alloc_wait_token (wsWgAddr s) γwg wsWgWGN 0 (by decide) $$ HisWg Hwt
    with ⟨-, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply wp_wsWg_Wait s γwg γd $$ [$Htok]
  · iframe #
  (try wp_auto)
  wp_apply (hClose st (γw.st.withPhys p) c) $$ [Hright]
  · rw [isStore_withPhys]
    iframe Hs
    iapply (storeCloserM_on st _ c hcm).2
    iexact Hright
  iapply HΦ; itrivial

end proof

end api
end mvcc
end EtcdGrove
end Perennial
