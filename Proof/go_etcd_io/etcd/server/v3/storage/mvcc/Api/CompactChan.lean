/-
**`compactChan.law`** (`Spec/.../mvcc/ApiCompactChan.lean`; mvccfull's Prove, 2026-11-10): `Compact`'s
contract with its channel made (`compactChanRecv`: not `nil`, its receive the pair), at `*store` and
`*watchableStore`. Lean-first (no Rocq counterpart). The proofs are `Api/CmpCb.lean`'s of
`KV.Compact.contract`, with the channel's facts from the broadcast channel's `isChan`
(`compactChan_recv`); a copy, so that `CmpCb` (and its importers) are unchanged.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiCompactChan
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiCompactChan
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpCb

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section core
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A compaction's channel, tracked, is made and can be received on (`compactChanRecv`). -/
theorem mvcc.compactChan_recv (ch : GoChan) (Qc : IProp GF) :
    mvcc.compactChan ch Qc ⊢ mvcc.api.compactChanRecv ch := by
  iintro #H
  iunfold mvcc.api.compactChanRecv
  iunfold mvcc.compactChan at H
  icases H with ⟨%γc, #Hb⟩
  ihave #Hic := ownBroadcastChan_is_chan _ _ _ _ $$ Hb
  ihave %Hnn := isChan_not_null $$ Hic
  isplitr
  · ipureintro; exact Hnn
  iintro !> %Φ !> - HΦ
  iapply (chan.wp_receive (V := Unit) ch γc)
  · iexact Hic
  iintro ⟨Hlc, -⟩
  iunfold recvAu
  imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc HΦ with HΦ
  ihave HR : recvAu (GF := GF) γc Unit (fun v ok => Φ (PairV #v #ok)) $$ [HΦ]
  · iapply broadcast_chan_receive _ _ _ _ _ $$ Hb
    iintro ⟨-, -⟩
    iapply HΦ
    itrivial
  iunfold recvAu at HR
  iexact HR

/-- `KV.Compact.contractC` at `*store #s` over what it uses of a plain store's handle (as
`CmpCb`'s `plain`). -/
private abbrev mvcc.store.Compact.plainC (s : Loc) : Prop :=
  ∀ (γ : mvcc.api.MvccName) (trace : Loc) (te : Bool) (rev : w64) (q : Qp) (B : mvcc.api.MvccStorage)
    (P : IProp GF) (f : GoFunc) (Pre Q' Post X Y : IProp GF) (Q : mvcc.api.MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      □ (mvcc.isStore s (γ : mvcc.StoreNames) ∗ mvcc.api.locIs (γ : mvcc.StoreNames).api s ∗
        mvcc.crevPermIs (γ : mvcc.StoreNames) (fun _ => iprop(True))) ∗
      mvcc.api.mvccOpen γ ∗ ⌜trace ≠ null⌝ ∗
      ⌜1 ≤ sint.Z rev⌝ ∗
      traceutil.ownTrace trace te ∗ mvcc.api.mvccBackend γ q B P ∗ mvcc.api.hookIs B f ∗
      X ∗ mvcc.api.storageReq B P X Y ∗
      Pre ∗ mvcc.api.hookRun P f Pre Q' ∗ (Q' ={⊤}=∗ P ∗ Post) ∗
      AU <{ ∃∃ (σ : mvcc.api.MvccState), mvcc.api.mvccState γ σ }> @ ⊤ \ ↑mvcc.api.mvccN, ∅
        <{ mvcc.api.mvccState γ (if σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)
              then σ.compactTo (sint.Z rev) else σ), COMM Q σ }> }}
    (App (App (Val #(methods (go.GoType.PointerType store.ty) go!"Compact" #s)) (Val #trace))
      (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err);
      mvcc.api.mvccOpen γ ∗ traceutil.ownTrace trace te ∗ mvcc.api.mvccBackend γ q B P ∗
      ∃ σ : mvcc.api.MvccState, Q σ ∗
      ((⌜err = GoInterface.nil ∧ σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)⌝ ∗ Post ∗ Y ∗
          mvcc.api.compactChanRecv ch) ∨
       (⌜sint.Z rev ≤ σ.crev⌝ ∗ globalAddr ErrCompacted ↦□ err ∗ Pre ∗ X ∗
          mvcc.api.compactChanRecv ch) ∨
       (⌜(σ.rev : Int) < sint.Z rev ∧ ch = chan.nil⌝ ∗ globalAddr ErrFutureRev ↦□ err ∗ Pre ∗ X)) }}

/-- `KV.Compact.contract`'s body at a plain store's handle, from the core (its location and
permit `True`). -/
private theorem mvcc.store.Compact.wp_plainC (hcore : mvcc.store.Compact.core (GF := GF) (hG := hG)) :
    ∀ s : Loc, mvcc.store.Compact.plainC (GF := GF) s := by
  intro s (γ : mvcc.StoreNames) trace te rev q B P f Pre Q' Post X Y Q
  iintro %Φ ⟨#Hpkg, #Hmv, Hopen, %htr, %hpos1, Htrc, HB, #Hhk, HX, #Hreq, HPre, Hrun, Hupd, HAU⟩
    HΦ
  icases Hmv with ⟨#Hs, #Hloc, #Hperm⟩
  iunfold mvcc.api.mvccState at HAU
  -- the open token, at the store's location and current names
  iunfold mvcc.api.mvccOpen at Hopen
  icases Hopen with ⟨%s2, %p, %c, #Hloc2, Hright, Hcra, HRT, #Hsup, %hc, Hor, Hwo⟩
  ihave %Hss := mvcc.api.locIs_agree _ _ _ $$ [Hloc Hloc2]
  · isplitl
    · iexact Hloc
    · iexact Hloc2
  cases Hss
  -- the backend share: its names are the right's
  iunfold mvcc.api.mvccBackend at HB
  icases HB with ⟨HF, %p', %o', %d, Hcur', %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
  obtain ⟨hpk, hcm, rfl⟩ := Hd
  rw [show (mvcc.api.storageReq d P X Y : IProp GF) = backend.commitReq d.γB d.P P d.be X Y from rfl,
    show (mvcc.api.hookIs d f : IProp GF) = backend.plHookRO d.γB f from rfl]
  icases (mvcc.compactRightR_iff s ((γ : mvcc.StoreNames).withPhys p) c).1 $$ Hright with
    ⟨Hcr, Hq, %o, ⟨Hfs, #Hsc, Hstc, Htok⟩, #Hstop⟩
  icases mvcc.fieldShareAt_cur s ((γ : mvcc.StoreNames).withPhys p) _ o $$ Hfs with ⟨Hcur, Hfsb⟩
  ihave %Hv := mvcc.curAt_agree ((γ : mvcc.StoreNames).withPhys p) ((γ : mvcc.StoreNames).withPhys p')
      rfl _ _ o o' $$ [Hcur Hcur']
  · isplitl [Hcur]
    · iexact Hcur
    · iexact Hcur'
  obtain ⟨-, hp⟩ := Hv
  have hp' : p = p' := hp
  subst hp'
  ihave Hfs := Hfsb $$ Hcur
  ihave Hright : mvcc.compactRightR (GF := GF) s ((γ : mvcc.StoreNames).withPhys p) c
      $$ [Hcr Hq Hfs Hstc Htok]
  · iapply (mvcc.compactRightR_iff s ((γ : mvcc.StoreNames).withPhys p) c).2
    iframe Hcr Hq
    iexists o
    iframe Hfs Hsc Hstc Htok Hstop
  -- the store's compaction facts at its current names
  have hkb : ((γ : mvcc.StoreNames).withPhys p).kb = some d := hpk
  have hcmp : mvcc.storeCmp ((γ : mvcc.StoreNames).withPhys p) := by
    show mvcc.kbCmpM ((γ : mvcc.StoreNames).withPhys p).kb
    rw [hkb]; exact hcm
  ihave #HpR : mvcc.crevPermAt (GF := GF) ((γ : mvcc.StoreNames).withPhys p) (sint.Z rev) $$ []
  · iapply mvcc.crevPermAt_of _ (fun _ => iprop(True))
    isplitl
    · iapply (mvcc.crevPermIs_cperm (γ : mvcc.StoreNames) ((γ : mvcc.StoreNames).withPhys p) rfl
        (fun _ => iprop(True)))
      iexact Hperm
    · iintro !>; itrivial
  ihave #HreqS : mvcc.storeReq (GF := GF) ((γ : mvcc.StoreNames).withPhys p) X Y $$ []
  · simp only [mvcc.storeReq, mvcc.StoreNames.withPhys_kb, hpk]
    iunfold mvcc.kbReq
    iunfold mvcc.bkReq
    iright
    iexists (mvcc.lateW d.gx), P
    iframe Hbk Hreq
  ihave #Hsup' : mvcc.kbWTSupplyM (GF := GF) ((γ : mvcc.StoreNames).withPhys p).kb $$ []
  · rw [mvcc.StoreNames.withPhys_kb]; iexact Hsup
  -- the hook's context: set, the hook's facts and the caller's contract; nil, the unset arm
  ihave ⟨%hk, %dq, Hctx⟩ : (∃ (hk : Option val) (dq : DFrac),
      mvcc.lockCtxM (GF := GF) ((γ : mvcc.StoreNames).withPhys p) P hk Pre Q' Post dq)
      $$ [HPre Hrun Hupd]
  · by_cases hf : f = func.nil
    · iexists none, DFrac.discard
      rw [mvcc.lockCtxM_none]
      iunfold mvcc.api.hookRun at Hrun
      simp only [hf, ↓reduceIte]
      iframe Hhp HPre
      isplitr
      · rw [mvcc.StoreNames.withPhys_kb, hpk]
        iunfold mvcc.kbHookNilAt
        rw [← hf]; iexact Hhk
      iintro HPP
      imod Hrun $$ HPP with HQ'
      iapply Hupd $$ HQ'
    · iexists (some #f), DFrac.discard
      rw [mvcc.lockCtxM_some]
      iunfold mvcc.api.hookRun at Hrun
      simp only [hf, ↓reduceIte]
      icases Hrun with #Hrun
      isplitr
      · iunfold mvcc.hookOk
        iframe Hhp
        iunfold mvcc.hookFn
        rw [mvcc.StoreNames.withPhys_kb, hpk]
        iunfold mvcc.kbHookIs
        iunfold mvcc.bkHookIs
        iexists f
        iframe Hhk
        ipureintro; exact ⟨rfl, hf⟩
      iunfold mvcc.csContract
      iframe HPre Hrun Hupd
  -- the client's update, the store's ghost step
  ihave Hcb := mvcc.compact_cmpCb γ p c (sint.Z rev) hpos1 Q $$ [Hcra HAU]
  · iframe Hcra HAU
  iapply (hcore s ((γ : mvcc.StoreNames).withPhys p) trace rev c P hk dq Pre Q' Post
      (mvcc.api.shareTok (γ : mvcc.StoreNames).api q)
      iprop(mvcc.api.crevAuth (γ : mvcc.StoreNames).api (1 : Qp).half.half (sint.Z rev) ∗
        ∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)⌝)
      iprop(mvcc.api.crevAuth (γ : mvcc.StoreNames).api (1 : Qp).half.half c ∗
        ∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜sint.Z rev ≤ σ.crev⌝)
      iprop(mvcc.api.crevAuth (γ : mvcc.StoreNames).api (1 : Qp).half.half c ∗
        ∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜(σ.rev : Int) < sint.Z rev⌝)
      X Y te htr hcmp hc hpos1
      (mvcc.slotF_share_excl (γ := (γ : mvcc.StoreNames).withPhys p) rfl q)
      (mvcc.slotFr_share_excl ((γ : mvcc.StoreNames).withPhys p) q))
    $$ [Hright Hctx Htrc HRT HF Hcb HX] [-]
  · rw [mvcc.isStore_withPhys]
    iframe #
    iframe Hright Hctx Htrc HRT HF Hcb HX
  inext
  iintro %ch %err ⟨Htrc, HRT, -, HF, Hres⟩
  ihave HB : mvcc.api.mvccBackend (GF := GF) γ q d P $$ [HF Hcur']
  · iunfold mvcc.api.mvccBackend
    iframe HF
    iexists p, o', d
    iframe Hcur' Hbk Hrg Hhp Hwts
    ipureintro; exact ⟨⟨hpk, hcm, rfl⟩, Hlp⟩
  icases Hres with (⟨⟨%Herr, %Hlt⟩, Hright, #Hlb, HPost, #Hch, ⟨Hcra, %σ, HQ, %Hσ⟩, HYB⟩ |
    ⟨%Hle, ⟨%ec, #Hec, %Herr⟩, Hright, HPre, #Hch, ⟨Hcra, %σ, HQ, %Hσ⟩, HXB⟩ |
    ⟨%Hch, ⟨%ef, #Hef, %Herr⟩, Hright, HPre, ⟨Hcra, %σ, HQ, %Hσ⟩, HXB⟩)
  · iapply HΦ
    iframe Htrc HB
    isplitl [Hright Hcra HRT Hor Hwo]
    · iunfold mvcc.api.mvccOpen
      iexists s, p, (sint.Z rev)
      iframe Hloc Hright Hcra HRT Hsup Hor Hwo
      ipureintro; omega
    iexists σ
    iframe HQ
    ileft
    iframe HPost HYB
    isplitr
    · ipureintro; exact ⟨Herr, Hσ⟩
    iapply mvcc.compactChan_recv; iexact Hch
  · subst Herr
    iapply HΦ
    iframe Htrc HB
    isplitl [Hright Hcra HRT Hor Hwo]
    · iunfold mvcc.api.mvccOpen
      iexists s, p, c
      iframe Hloc Hright Hcra HRT Hsup Hor Hwo
      ipureintro; exact hc
    iexists σ
    iframe HQ
    iright
    ileft
    iframe HPre HXB Hec
    isplitr
    · ipureintro; exact Hσ
    iapply mvcc.compactChan_recv; iexact Hch
  · subst Herr
    iapply HΦ
    iframe Htrc HB
    isplitl [Hright Hcra HRT Hor Hwo]
    · iunfold mvcc.api.mvccOpen
      iexists s, p, c
      iframe Hloc Hright Hcra HRT Hsup Hor Hwo
      ipureintro; exact hc
    iexists σ
    iframe HQ
    iright
    iright
    iframe HPre HXB Hef
    ipureintro; exact ⟨Hσ, Hch⟩

/-- **`KV.Compact.contractC` at `*store`**, from the core: the handle a plain store's. -/
theorem mvcc.store.Compact.wp_apiC (hcore : mvcc.store.Compact.core (GF := GF) (hG := hG)) :
    ∀ s : Loc, mvcc.api.KV.Compact.contractC (GF := GF) (go.GoType.PointerType store.ty) #s := by
  intro s (γ : mvcc.StoreNames) trace te rev q B P f Pre Q' Post X Y Q
  iintro %Φ ⟨#Hpkg, Hmv, Hrest⟩ HΦ
  iunfold mvcc.api.isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  rotate_left 1
  · iunfold mvcc.api.isMvccWatchable at Hmv
    icases Hmv with ⟨%s', %st, %γw, %Hk, -⟩
    exfalso
    obtain ⟨Hk, -⟩ := Hk
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold mvcc.api.isMvccPlain at Hmv
  icases Hmv with ⟨%s', %Hk, #Hs, #Hloc, #Hperm, -⟩
  have hs : s = s' := mvcc.mkOk_loc_inj _ Hk
  cases hs
  iapply (mvcc.store.Compact.wp_plainC hcore s γ trace te rev q B P f Pre Q' Post X Y Q) $$ [Hrest] HΦ
  isplitl []
  · iexact Hpkg
  isplitl []
  · iintro !>; iframe Hs Hloc Hperm
  iexact Hrest

/-- **`KV.Compact.contractC` at `*watchableStore`**: the promoted method, the inner store's
(`store.Compact.spec` at it: the handle's inner store, its location and permit). -/
theorem mvcc.watchableStore.Compact.wp_proofC (hcore : mvcc.store.Compact.core (GF := GF) (hG := hG)) :
    ∀ s : Loc, mvcc.api.KV.Compact.contractC (GF := GF) (go.GoType.PointerType watchableStore.ty) #s := by
  intro s (γ : mvcc.StoreNames) trace te rev q B P f Pre Q' Post X Y Q
  wp_start as ⟨Hmv, Hrest⟩
  iunfold mvcc.api.isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  · iunfold mvcc.api.isMvccPlain at Hmv
    icases Hmv with ⟨%s', %Hk, -⟩
    exfalso
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold mvcc.api.isMvccWatchable at Hmv
  icases Hmv with ⟨%s', %st, %γw, %Hk, #Hws, -, #Hrp, #Hloc, #Hperm, #Hfree⟩
  obtain ⟨Hk, hγ⟩ := Hk
  rw [interface_mkOk_inj] at Hk
  have hs : s = s' := go.intoVal_inj Hk.2
  subst hs
  ihave #Hws' := Hws
  iunfold mvcc.isWatchableStore at Hws'
  icases Hws' with ⟨%vc, %stc, %rv, %γv, Hws'⟩
  iNamed Hws'
  ihave #Hmvs : □ (mvcc.isStore (GF := GF) st (γ : mvcc.StoreNames) ∗
      mvcc.api.locIs (γ : mvcc.StoreNames).api st ∗
      mvcc.crevPermIs (γ : mvcc.StoreNames) (fun _ => iprop(True))) $$ []
  · iintro !>
    rw [← hγ]
    iframe Hs Hloc Hperm
  (try wp_auto)
  wp_apply (mvcc.store.Compact.wp_plainC hcore st γ trace te rev q B P f Pre Q' Post X Y Q) $$ [Hrest Hmvs] as %ch %err HQ
  · iframe #
    iexact Hrest
  iapply HΦ; iexact HQ


/-- **`compactChan.law`**, from the core: a handle is a plain store's or a watchable store's. -/
theorem mvcc.api.compactChan.law_holds (hcore : mvcc.store.Compact.core (GF := GF) (hG := hG)) :
    mvcc.api.compactChan.law (GF := GF) := by
  intro ty v γ
  iintro Hmv
  iunfold mvcc.api.isMvcc at Hmv
  icases Hmv with #(⟨Hmv, -⟩ | Hmv)
  · iunfold mvcc.api.isMvccPlain at Hmv
    icases Hmv with ⟨%s, %Hk, -⟩
    rw [interface_mkOk_inj] at Hk
    obtain ⟨rfl, rfl⟩ := Hk
    ipureintro; exact mvcc.store.Compact.wp_apiC hcore s
  · iunfold mvcc.api.isMvccWatchable at Hmv
    icases Hmv with ⟨%s, %st, %γw, %Hk, -⟩
    obtain ⟨Hk, -⟩ := Hk
    rw [interface_mkOk_inj] at Hk
    obtain ⟨rfl, rfl⟩ := Hk
    ipureintro; exact mvcc.watchableStore.Compact.wp_proofC hcore s

end core

end EtcdGrove
end Perennial
