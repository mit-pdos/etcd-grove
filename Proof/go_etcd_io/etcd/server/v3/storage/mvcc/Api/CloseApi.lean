/-
**`KV.Close.contract` at both store types** (track A, 2026-11-06; its post `mvccClosed`, the reader
tokens, 2026-11-06). Lean-first (no Rocq counterpart). Over the sealed definitions of `Api.lean`
(imported with `import all`).

* `store.Close.wp_api`: a plain store's `Close` from `store.Close.spec`: the open token at the store's
  location and current names gives the restorable compaction right, the store's right to close in
  compaction mode (`storeCloserM_on`, by `openRest`'s mode); `mvccClosed` from the open token's
  retired readers, its two tickets (`openRest`) and `store.Close`'s post (the job's reader, the
  closer's part of the current names).
* `watchableStore.Close.wp_api`: a watchable store's, as `watchableStore.Close.wp_proof` (its stop
  channel closed, the loops waited for, their readers taken, the inner store closed), with the
  watchable store's own closer from the open token's `openRest` (found through the inner store's read
  view, which points at the receiver) and the inner store's right as the plain store's; the loops'
  two readers' tickets in `mvccClosed`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RdSupply

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
compaction mode, the compactor's retired reader, the writer's own (`writerOwn`), and the rest of
`openRest`. -/
private theorem mvccOpen_at (γ : mvcc.StoreNames) (s : Loc) :
    api.locIs γ.api s ∗ mvccOpen (GF := GF) γ ⊢
      ∃ (p : PhysNames) (c : Int), compactRightR s (γ.withPhys p) c ∗
        ⌜kbCmpM (γ.withPhys p).kb⌝ ∗ storeRT (γ.withPhys p) ∗ writerOwn (γ.withPhys p) ∗
        (if γ.watchQ then iprop(∃ (w rv stc : Loc),
          s.[store, go!"ReadView"] ↦□
            (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
          rv.[readView, go!"kv"] ↦□
            (interface.mkOk (go.GoType.PointerType watchableStore.ty) #w : GoInterface) ∗
          w.[watchableStore, go!"stopc"] ↦□ stc ∗ stopCloser stc ∗ wsWaiter w s γ)
        else iprop(ownToks γ.tk 2)) := by
  iintro ⟨#Hloc, Hopen⟩
  iunfold mvccOpen at Hopen
  icases Hopen with ⟨%s2, %p, %c, #Hloc2, Hright, -, HRT, -, -, Hor, Hwo⟩
  ihave %Hss := api.locIs_agree γ.api s s2 $$ [Hloc Hloc2]
  · iframe Hloc Hloc2
  cases Hss
  iunfold openRest at Hor
  icases Hor with ⟨%hcm, Hw⟩
  iexists p, c
  iframe Hright HRT Hwo
  isplitr
  · ipureintro; simp only [StoreNames.withPhys_kb]; exact hcm
  cases hw : γ.watchQ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hw with ⟨-, -, Ht⟩
    iexact Ht
  · simp only [↓reduceIte]
    iexact Hw

/-- **`mvccClosed`, assembled** from the store's pool, a part of the current names, the open
token's retired readers, two tickets, the job's reader and the pool of the reader tokens. -/
private theorem mvccClosed_of (γ : mvcc.StoreNames) (p : PhysNames) (dq : DFrac) (o : StoreObjs) :
    £ 1 ∗ readerPool (GF := GF) γ ∗ curAt (γ.withPhys p) dq o ∗ storeRT (γ.withPhys p) ∗
      writerOwn (γ.withPhys p) ∗ ownToks γ.tk 2 ∗ compactJobResM (γ.withPhys p).kb ∗
      (∃ R : IProp GF, rdkPool γ R) ⊢
      mvccClosed (γ : MvccName) := by
  iintro ⟨Hlc, #Hpool, Hcur, HRT, Hwo, Ht, Hjob, Hrk⟩
  iunfold writerOwn at Hwo
  icases Hwo with ⟨HRTw, Hret⟩
  iunfold mvccClosed
  iexists p, dq, o
  iframe Hlc Hpool Hcur HRT HRTw Hret Ht Hjob Hrk

/-- **`KV.Close.contract` at `*store`.** -/
theorem store.Close.wp_api (hClose : mvcc.store.Close.spec (GF := GF) (hG := hG)) :
    store.Close.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames)
  iintro %Φ ⟨#Hpkg, Hmv, Hopen⟩ HΦ
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  rotate_left 1
  · iunfold isMvccWatchable at Hmv
    icases Hmv with ⟨%s', %st, %γw, %Hk, -⟩
    exfalso
    obtain ⟨Hk, -⟩ := Hk
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccPlain at Hmv
  icases Hmv with ⟨%s', %Hk, #Hs, #Hloc, -, #Hsup, -⟩
  have hs : s = s' := mkOk_loc_inj _ Hk
  subst hs
  iunfold rdSupply at Hsup
  icases Hsup with ⟨%R, #Hrk, -⟩
  icases mvccOpen_at γ s $$ [Hloc Hopen] with ⟨%p, %c, Hright, %hcm, HRT, Hwo, Ht⟩
  · iframe Hloc Hopen
  rw [Hwq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ihave #Hs0 := Hs
  iunfold isStore at Hs0
  iNamed Hs0
  wp_apply (hClose s (γ.withPhys p) c) $$ [Hright] as ⟨Hjob, Hlc1, %dq, %o, Hcur⟩
  · rw [isStore_withPhys]
    iframe Hs
    iapply (storeCloserM_on s _ c hcm).2
    iexact Hright
  iapply HΦ
  ihave Hjob : compactJobResM (GF := GF) (γ.withPhys p).kb $$ [Hjob]
  · simp only [StoreNames.withPhys_kb]; iexact Hjob
  ihave Hcur : curAt (GF := GF) (γ.withPhys p) dq o $$ [Hcur]
  · iexact Hcur
  iapply mvccClosed_of γ p dq o $$ [$Hlc1 $Hpool $Hcur $HRT $Hwo $Ht $Hjob]
  iexists R; iexact Hrk

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
  icases Hmv with ⟨%s', %st, %γw, %Hk, #Hws, -, #Hrk, #Hloc, -⟩
  obtain ⟨Hk, hγ⟩ := Hk
  subst hγ
  rw [interface_mkOk_inj] at Hk
  have hs : s = s' := go.intoVal_inj Hk.2
  subst hs
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isWatchableStore at Hws
  iNamed Hws
  icases mvccOpen_at γw.st st $$ [Hloc Hopen] with ⟨%p, %c, Hright, %hcm, HRT, Hwo, Hw⟩
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
  ihave #Hs0 := Hs
  iunfold isStore at Hs0
  iNamed Hs0
  iunfold stopCloser at Hstop
  icases Hstop with ⟨%γc, Hstop⟩
  iunfold wsWaiter at Hwait
  icases Hwait with ⟨%γwg, %γd, %γx, #HisWg, #Hinv, Hwt, Hγx⟩
  wp_auto_lc 1
  wp_apply wp_broadcast_chan_close stc γc iprop(True) $$ [$Hstop] as -
  · imodintro; itrivial
  (try wp_auto)
  iapply fupd_wp
  imod fupd_mask_subseteq (E2 := ↑wsWgWGN) CoPset.subseteq_top with Hmask
  imod sync.alloc_wait_token (wsWgAddr s) γwg wsWgWGN 0 (by decide) $$ HisWg Hwt
    with ⟨-, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply mvcc.wp_wsWg_Wait s st γw.st γwg γd γx $$ [$Htok $Hγx] as Hrds
  · iframe #
  (try wp_auto)
  -- the loops' readers' tickets
  rw [show wsLoopN = 1 + 1 from rfl, List.replicate_succ, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hr1, Hrds⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hr2, -⟩
  iunfold storeReader at Hr1 Hr2
  icases (mvcc.storeReaderC_split st γw.st).1 $$ Hr1 with ⟨-, Ht1⟩
  icases (mvcc.storeReaderC_split st γw.st).1 $$ Hr2 with ⟨-, Ht2⟩
  ihave Ht : ownToks (GF := GF) γw.st.tk 2 $$ [Ht1 Ht2]
  · iapply (ownToks_add 1 1 γw.st.tk).2; iframe Ht1 Ht2
  wp_apply (hClose st (γw.st.withPhys p) c) $$ [Hright] as ⟨Hjob, -, %dq, %o, Hcur⟩
  · rw [isStore_withPhys]
    iframe Hs
    iapply (storeCloserM_on st _ c hcm).2
    iexact Hright
  iapply HΦ
  ihave Hjob : compactJobResM (GF := GF) (γw.st.withPhys p).kb $$ [Hjob]
  · simp only [StoreNames.withPhys_kb]; iexact Hjob
  iapply mvccClosed_of γw.st p dq o $$ [$Hlc1 $Hpool $Hcur $HRT $Hwo $Ht $Hjob]
  iexists _; iexact Hrk

end proof

end api
end mvcc
end EtcdGrove
end Perennial
