/-
**The watchable store's transactions: `KV.Read`/`KV.Write` at `*watchableStore`, `Txn.End` at
`*watchableStoreTxnWrite`** (M4, track B, 2026-11-06). Lean-first (no Rocq counterpart). Over the
sealed definitions of `Api.lean` (imported with `import all`).

* `KV.Read` (the inner store's, promoted): the reader from the handle's readers' pool
  (`isMvccWatchable`'s, of `watchReader`s: the inner store's reader and one of the watchable
  store's `s.mu` slots, which the thread token's way back keeps, `tokBack`), then `ReadApi`'s step.
* `KV.Write` (`watchableStore.Write`'s code, over the inner store's `store.Write`): the reader from
  the pool, the inner store at the backend share's current physical names, the hook by its state
  (`writeCtxM`), the begin's step from the client's update (`writeCb_of_au`); the transaction the
  wrapper of the inner one, at the watchable store's names with the current physical names.
  **Conditional on track A's handle contents** (`wwriterHyp`, a hypothesis of the theorem, not an
  axiom: the certificate map's free entry, the write-back supply and the sole writer's certificate,
  tokens, notified-log half and pin, which track A puts into the handle and the writer's state).
* `Txn.End` at `*watchableStoreTxnWrite` (`watchableStoreTxnWrite.End.spec`): the backend share's
  names are the transaction's, its `hookP`, the frozen state excluded by the share's token, the
  notify and commit steps from the client's update (`wsEndCbY_of_au`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WsEndSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Instance
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.ReadApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WriteApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStoreTxnWrite__End

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

/-- **A write transaction's physical names are those of any share of the store's current objects**
(the transaction's `s.mu` share's objects agree with the share's). -/
theorem isTxnWriteT_names (mw s : Loc) (γ : StoreNames) (p p' : PhysNames) (trace : Loc)
    (ilog : Log) (pend : List Change) (puts deletes putSize : w64) (crev : Int) (Z : IProp GF)
    (ld : Bool) (Tr : IProp GF) (dq : DFrac) (o' : StoreObjs) :
    isTxnWriteT (GF := GF) mw s (γ.withPhys p) trace ilog pend puts deletes putSize crev Z ld Tr ∗
      curAt (γ.withPhys p') dq o' ⊢
      isTxnWriteT mw s (γ.withPhys p) trace ilog pend puts deletes putSize crev Z ld Tr ∗
        curAt (γ.withPhys p') dq o' ∗ ⌜p = p'⌝ := by
  iintro ⟨H, Hc⟩
  iunfold isTxnWriteT at H
  iNamed H
  iunfold storeTxnWriteIs at Htw
  iNamed Htw
  icases muHeld_cur s (γ.withPhys p) crev ti $$ Hmu with ⟨%o, %Ho, Hpin, Hmub⟩
  ihave %Hv := curAt_agree (γ.withPhys p) (γ.withPhys p') rfl _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  ihave Hmu := Hmub $$ Hpin
  iframe Hc
  isplitl
  · iunfold isTxnWriteT
    iexists tw, ranges
    iframe Hmw Htrc
    iunfold storeTxnWriteIs
    iexists ti, bt, Locked, chs, ps, ntok, Pw, fw, Dep
    simp only [named]
    iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hwv HY Htko Hmu HrevMu Hti Hrt
      Hcres Hlrd
    iframe #
    ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩
  ipureintro; exact Hv.2

/-- The watchable handle's reader, for a thread token, with its way back (the pool's loan and the
watchable store's `s.mu` slot kept). -/
theorem watchReader_borrow (s st : Loc) (γw : WsNames) (γp : GName) :
    £ 1 ∗ threadPool.isThreadPool watchRdPoolN γp (watchReader s st γw) ∗ threadTok ⊢
      |={⊤}=> storeReaderC st γw.st ∗ tokBack st γw.st := by
  iintro ⟨Hlc, #Hrp, Htok⟩
  imod threadPool.borrow_lc watchRdPoolN γp _ ⊤ (fun _ _ => CoPset.mem_full)
    $$ [$Hlc $Hrp $Htok] with ⟨HPR, Hloan⟩
  iunfold watchReader at HPR
  icases HPR with ⟨Hrd, Hslot⟩
  imodintro
  isplitl [Hrd]
  · iapply storeReader_toC; iexact Hrd
  iunfold tokBack
  iintro Hrd
  iapply threadPool.giveBack watchRdPoolN γp _ ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hrp $Hloan Hrd Hslot]
  iunfold watchReader
  iframe Hslot
  iapply storeReader_of; iexact Hrd

/-- **`KV.Read.contract` at `*watchableStore`.** -/
theorem watchableStore.Read.wp_api (hR : mvcc.store.Read.spec (GF := GF) (hG := hG)) :
    watchableStore.Read.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) mode trace te Q
  wp_start as ⟨Hmv, Htok, %Htrnn, Htrc, Hau⟩
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
  ihave #Hs0 := Hs
  iunfold isStore at Hs0
  iNamed Hs0
  wp_auto_lc 1
  iapply fupd_wp
  imod watchReader_borrow s st γw γp $$ [$Hlc1 $Hrp $Htok] with ⟨Hrd, Hback⟩
  imod crevLb_neg γw.st.idx with #Hlb
  imod ownToks_0 (GF := GF) γw.st.revs with Hnone
  iunfold mvccState at Hau
  ihave Hcb := readCbC_of_au γw.st Q $$ Hau
  ihave #HZ : □ (iprop(True) : IProp GF) $$ []
  · iintro !>; itrivial
  ihave Hla : logLent (GF := GF) γw.st.idx none $$ []
  · unfold logLent; itrivial
  imodintro
  wp_apply (hR st γw.st mode trace 0 [[], []] te (-1) iprop(True) none
      (fun L c => iprop(∃ σ : MvccState, Q σ ∗ ⌜σ.log = L ∧ σ.crev = c ∧ MvccReachable σ⌝)))
    $$ [Hrd Hnone Htrc Hla Hcb]
    as %mw ⟨%log, %rev, %crev, Htx, Htrc, -, -, -, -, %Hpre0, -, -, ⟨%σ, HQ, %Hσ⟩⟩
  · iframe Hs Hrd Hnone Htrc Hla Hcb HZ Hc0 Hlb
    ipureintro; exact Htrnn
  obtain ⟨hl, hc, hre⟩ := Hσ
  subst hl hc
  icases isTxnReadT_rev _ _ _ _ _ _ _ _ _ $$ Htx with ⟨Htx, %Hrev⟩
  subst Hrev
  iapply HΦ
  iframe Htrc
  iexists σ
  iframe HQ
  iunfold mvccTxn
  simp only [mvccTxnI]
  iexists mw, st, 0
  iframe Htx Hback
  isplitr
  · ipureintro; exact hre
  iapply roWrap_zero

/-- **What a writer of a watchable store needs of its handle** (track A's request 3), at the inner
store's physical names `p`: the certificate map's free entry, the write-back supply, and the sole
writer (its certificate, tokens, notified-log half and pin) at a log with room for a revision. -/
def wwriterRes (γw : WsNames) (p : PhysNames) : IProp GF :=
  iprop(certFree (γw.st.withPhys p) ∗ storeWT (γw.st.withPhys p) ∗
    ∃ L : Log, watchWriter (γw.withPhys p) L ∗ ⌜L.length + 4 ≤ 2 ^ 63⌝)

/-- **The hypothesis**: a watchable handle's store gives a writer its resources, at any physical
names (false of today's `isMvccWatchable`; track A's handle contents make it a law of the
handle). -/
abbrev wwriterHyp : Prop :=
  ∀ (s st : Loc) (γw : WsNames) (p : PhysNames),
    isWatchableStore (GF := GF) s st γw ⊢ |={⊤}=> wwriterRes γw p

/-- **`KV.Write.contract` at `*watchableStore`**, under `wwriterHyp`. -/
theorem watchableStore.Write.wp_api (hW : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hres : wwriterHyp (GF := GF)) :
    watchableStore.Write.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) trace te q B P Pre Q f R
  wp_start as ⟨Hmv, Htok, %Htrnn, Htrc, HB, #Hhk, Hpre, Hrun, Hau⟩
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
  ihave #Hws0 : isWatchableStore s st γw $$ []
  · iexact Hws
  iunfold isWatchableStore at Hws
  iNamed Hws
  -- the backend share at the store's current names
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p, %o, %d, Hcur, %Hd, #Hbk, #Hrg, #Hhp, #Hwts⟩
  obtain ⟨hpk, hcm, hdB⟩ := Hd
  subst hdB
  rw [show (hookIs d f : IProp GF) = backend.plHookRO d.γB f from rfl] at *
  -- the writer's resources (the hypothesis)
  imod hres s st γw p $$ Hws0 with Hres
  iunfold wwriterRes at Hres
  icases Hres with ⟨#Hfree, Hwt, ⟨%L, Hww, %Hlen⟩⟩
  iunfold watchWriter at Hww
  simp only [WsNames.withPhys_st]
  icases Hww with ⟨#Hcert, Htoks, Hwlog, Hpin⟩
  have hb : wBudget L = (wBudget L - 1) + 1 := by
    unfold wBudget; omega
  imod crevLb_neg (γw.st.withPhys p).idx with #Hlb
  -- the hook's context, by the frozen hook's state
  ihave ⟨%hk, %dq, Hctx⟩ : (∃ (hk : Option val) (dq : DFrac),
      writeCtxM (GF := GF) (γw.st.withPhys p) P hk Pre Q dq) $$ [Hpre Hrun]
  · by_cases hf : f = func.nil
    · iexists none, DFrac.discard
      rw [writeCtxM_none]
      iunfold hookRun at Hrun
      simp only [hf, ↓reduceIte]
      iframe Hhp Hpre Hrun
      rw [StoreNames.withPhys_kb, hpk]
      iunfold kbHookNilAt
      rw [← hf]; iexact Hhk
    · iexists (some #f), DFrac.discard
      rw [writeCtxM_some]
      iunfold hookRun at Hrun
      simp only [hf, ↓reduceIte]
      icases Hrun with #Hrun
      iframe Hpre Hrun
      iunfold hookOk
      iframe Hhp
      iunfold hookFn
      rw [StoreNames.withPhys_kb, hpk]
      iunfold kbHookIs
      iunfold bkHookIs
      iexists f
      iframe Hhk
      ipureintro; exact ⟨rfl, hf⟩
  -- the begin's step, from the client's update
  iunfold mvccState at Hau
  ihave Hcb := writeCb_of_au γw.st p R $$ Hau
  ihave #Hx : □ (slotF (γw.st.withPhys p) ∗ api.shareTok γw.st.api q -∗ False) $$ []
  · iintro !> H
    iapply (slotF_share_excl (γ := γw.st.withPhys p) (a := γw.st.api) rfl q) $$ H
  ihave #HZ : □ (iprop(True) : IProp GF) $$ []
  · iintro !>; itrivial
  rw [hb]
  icases (ownToks_add 1 (wBudget L - 1) _).1 $$ Htoks with ⟨Htoks, H1⟩
  -- the reader, from the pool
  wp_auto_lc 1
  iapply fupd_wp
  imod watchReader_borrow s st γw γp $$ [$Hlc1 $Hrp $Htok] with ⟨Hrd, Hback⟩
  imodintro
  wp_apply (hW st (γw.st.withPhys p) trace P Pre Q hk dq te (-1) iprop(True) L _ o
      (api.shareTok γw.st.api q)
      (fun L c => iprop(∃ σ : MvccState, R σ ∗
        ⌜σ.log = L ∧ σ.crev = c ∧ σ.pending = none ∧ MvccReachable σ⌝)))
    $$ [Hrd H1 Hwt Hctx Hcur HF Hcb Hpin Htrc]
    as %mw ⟨⟨%ilog, %crev, Htx, -, -, -, ⟨%σ, HR, %Hσ⟩⟩, Htrc, HQ, -, Hcur, HF⟩
  · rw [isStore_withPhys, storeReaderC_withPhys]
    iframe Hs Hrd Hwt Hctx Hcur HF Hcb Hpin Htrc Hx HZ Hlb
    unfold revToken; iframe H1
    ipureintro; exact Htrnn
  obtain ⟨hl, hc, hpn, hre⟩ := Hσ
  subst hl hc
  -- the sole writer pins the transaction's committed log
  iunfold isTxnWriteT at Htx
  iNamed Htx
  ihave %Heq := watchWriter_pins (γw.st.withPhys p) L σ.log [] tw st σ.crev $$ [$Hcert $Htoks $Htw]
  subst Heq
  ihave Htx : isTxnWriteT mw st (γw.st.withPhys p) trace σ.log [] (W64 0) (W64 0) (W64 0) σ.crev
      iprop(True) false iprop(True) $$ [Hmw Htw Htrc]
  · iunfold isTxnWriteT; iexists tw, ranges; iframe
  (try wp_auto)
  wp_alloc wtw as Hwtw
  ipersist Hwtw
  (try wp_auto)
  iapply HΦ
  iframe Htrc HQ
  isplitl [HF Hcur]
  · iunfold mvccBackend
    iframe HF
    iexists p, o, d
    iframe Hcur Hbk Hrg Hhp Hwts
    ipureintro; exact ⟨hpk, hcm, rfl⟩
  iexists σ
  iframe HR
  iunfold mvccTxn
  simp only [mvccTxnI]
  iexists mw, st, p, (W64 0), (W64 0), (W64 0)
  iframe Htx Hfree
  isplitr
  · ipureintro; exact ⟨hpn, hre⟩
  isplitl [Hback]
  · rw [show tokBack (GF := GF) st (γw.st.withPhys p) = tokBack st γw.st from rfl]; iexact Hback
  iunfold wrWrap
  iright
  iexists wtw, s, (γw.withPhys p)
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iunfold wsWrap
  rw [isWatchableStore_withPhys]
  simp only [WsNames.withPhys_st]
  iframe Hwtw Hcert Htoks Hwlog Hws0

/-- **`Txn.End.contract` at `*watchableStoreTxnWrite`.** -/
theorem watchableStoreTxnWrite.End.wp_api
    (hEnd : mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG)) :
    watchableStoreTxnWrite.End.spec (GF := GF) := by
  intro t0 (γ : mvcc.StoreNames) trace k q B P Q
  iintro %Φ ⟨#Hpkg, Htx, Hk⟩ HΦ
  iapply wp_fupd
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, -, -, -, Hwrap⟩
    iexfalso
    iapply roWrap_pt n t0 mw $$ Hwrap
  | write σ₀ pend =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
    obtain ⟨Hpn, -⟩ := Hk0
    icases wrWrap_pt t0 _ s mw σ₀.log $$ Hwrap with ⟨%sw, %γw, %hγw, Hwrap⟩
    icases Hk with ⟨HB, HP, Hau⟩
    -- the backend share, at the transaction's names
    iunfold mvccBackend at HB
    icases HB with ⟨HF, %p', %o', %d, Hcur', %Hd, #Hbk, #Hrg, #Hhp, #Hwts⟩
    icases isTxnWriteT_names mw s γ p p' trace σ₀.log pend puts deletes putSize σ₀.crev iprop(True)
        false iprop(True) _ o' $$ [$Htx $Hcur'] with ⟨Htx, Hcur', %hpp⟩
    subst hpp
    ihave Htx : isTxnWriteT mw s γw.st trace σ₀.log pend puts deletes putSize σ₀.crev iprop(True)
        false iprop(True) $$ [Htx]
    · rw [hγw]; iexact Htx
    ihave #Hwq : ⌜γw.st.watchQ = true⌝ $$ [Hwrap]
    · iunfold wsWrap at Hwrap
      icases Hwrap with ⟨-, #Hws, -⟩
      iunfold isWatchableStore at Hws
      iNamed Hws
      ipureintro; exact Hwq
    icases Hwq with %Hwq
    ihave Htw := wsWrap_join t0 sw s γw mw trace σ₀.log pend puts deletes putSize σ₀.crev false
      iprop(True) $$ [$Hwrap $Htx]
    -- the steps from the client's update
    iunfold mvccState at Hau
    have hcb := wsEndCbY_of_au (GF := GF) γw σ₀ pend Q Hwq Hpn
    have ha : γw.st.api = γ.api := by rw [hγw]; rfl
    simp only [endAU, ha] at hcb
    ihave Hcb := hcb $$ Hau
    ihave #Hx : □ (slotF γw.st ∗ api.shareTok γ.api q -∗ False) $$ []
    · iintro !> H
      iapply (slotF_share_excl (γ := γw.st) (a := γ.api) ha q) $$ H
    ihave #Hok : certOkNext γw.st σ₀.log pend $$ []
    · rw [hγw]; iapply certFree_certOkNext; iexact Hfree
    ihave #Hhp' : hookP γw.st P $$ []
    · rw [hγw]; iexact Hhp
    wp_apply (hEnd trace t0 sw s γw σ₀.log pend puts deletes putSize P σ₀.crev false
        (api.shareTok γ.api q) Q iprop(True)) $$ [$Htw HP HF Hcb]
      as ⟨Hrd, -, -, -, HF, HQ⟩
    · iframe HP HF Hcb Hx Hok Hhp'
    iunfold tokBack at Hback
    ihave Hrd : storeReaderC s (γ.withPhys p) $$ [Hrd]
    · rw [← hγw]; iexact Hrd
    imod Hback $$ Hrd with Htok
    imodintro
    iapply HΦ
    iframe Htok HQ
    iunfold mvccBackend
    iframe HF
    iexists p, o', d
    iframe Hcur' Hbk Hrg Hhp Hwts
    ipureintro; exact Hd

end proof

end api
end mvcc
end EtcdGrove
end Perennial
