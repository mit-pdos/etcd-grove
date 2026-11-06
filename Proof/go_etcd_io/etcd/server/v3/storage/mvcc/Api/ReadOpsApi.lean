/-
**`KV.Rev` and `KV.FirstRev` at the two store types** (M4, track B, 2026-11-06). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

A store's `Rev()`/`FirstRev()` is its read view's (`readView.Rev`/`FirstRev`, promoted): a read
transaction of the view's `kv` (the store, or the watchable store over it: `kvOver`) with the
`TODO()` trace, its `Rev()`/`FirstRev()`, its deferred `End()`. The client's update fires at the
read (`readCbC_of_au`, through `kvOver_ReadCb`), the reader comes back through `tokBack`.
`store_Rev_cb`/`store_FirstRev_cb` are the store's, given its read view, a reader and its way back.
At `*watchableStore` the read view is the watchable store's (`isWatchableStore`) and the reader the
handle's pool's: **no hypothesis**. At `*store` the plain handle has neither the read view nor the
readers' pool yet: under `readerHyp` and `viewHyp` (track A's handle contents).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WatchTxnApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnOpsApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RangeApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KVView
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End

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

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- **`kv.Read(mode, trace)` of a KV over the store, with the read's callback** (`kvOver_Read`
with `F` in place of `readCbC_true`, the transaction without its trace). -/
theorem kvOver_ReadCb (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (ty : go.GoType) (v : val) (s : Loc) (γ : StoreNames) (mode : w32) (trace : Loc) (te : Bool)
    (F : Log → Int → IProp GF) :
    {{ pkgInit ∗ kvOver (interface.mkOk ty v) s ∗ isStore s γ ∗ storeReaderC s γ ∗
        ⌜trace ≠ null⌝ ∗ traceutil.ownTrace trace te ∗ readCbC γ F }}
      (App (App (Val #(methods ty go!"Read" v)) (Val #mode)) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
        ∃ (log : Log) (rev : w64) (crev : Int),
          isTxnReadT mw s γ trace log rev crev iprop(True) iprop(True) ∗ traceutil.ownTrace trace te ∗
          F log crev }} := by
  iintro %Φ ⟨#Hpkg, #Hk, #Hs, Hrd, %Ht, Htrc, Hcb⟩ HΦ
  iapply kvOver_read_wp ty v s mode trace
  iframe Hk
  imod crevLb_neg γ.idx with #Hlb
  imod ownToks_0 (GF := GF) γ.revs with Hnone
  ihave #Hs0 := Hs
  iunfold isStore at Hs0
  iNamed Hs0
  ihave #HZ : □ (iprop(True) : IProp GF) $$ []
  · iintro !>; itrivial
  ihave Hla : logLent (GF := GF) γ.idx none $$ []
  · unfold logLent; itrivial
  iapply (hRead s γ mode trace 0 [[], []] te (-1) iprop(True) none F) $$ [Hrd Hnone Htrc Hla Hcb]
  · iframe Hpkg Hs Hrd Hnone Htrc Hla Hcb HZ Hc0 Hlb; ipureintro; exact Ht
  inext
  iintro %mw ⟨%log, %rev, %crev, Htx, Htrc, -, -, -, -, -, -, -, HF⟩
  iapply HΦ
  iexists log, rev, crev
  iframe Htx Htrc HF

/-- The read's update, as the read's callback (at the store's names). -/
abbrev readAU (γ : StoreNames) (Q : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccStateI γ.api σ }> @ ⊤ \ ↑mvccN, ∅
    <{ mvccStateI γ.api σ, COMM Q σ }>)

/-- **A read view's `Rev()`, by the caller's update** (see the header). -/
theorem readView_Rev_cb (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (st rv : Loc) (γ : StoreNames) (Q : MvccState → IProp GF) :
    {{ pkgInit ∗ isReadView rv st γ ∗ storeReaderC st γ ∗ tokBack st γ ∗ readAU γ Q }}
      (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Rev")) (Val #()))
    {{ (r : w64), RET #r; threadTok ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 (σ.rev : Int)⌝ }} := by
  wp_start as ⟨#Hrv, Hrd, Hback, Hau⟩
  iapply wp_fupd
  iunfold isReadView at Hrv
  icases Hrv with ⟨%kv, Hrv⟩
  iNamed Hrv
  ihave %Hkvok := kvOver_ok kv st $$ Hkvo
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  ihave Hcb := readCbC_of_au γ Q $$ Hau
  wp_apply (kvOver_ReadCb hRead kty kvv st γ _ t true
      (fun L c => iprop(∃ σ : MvccState, Q σ ∗ ⌜σ.log = L ∧ σ.crev = c ∧ MvccReachable σ⌝)))
      $$ [Hrd Htrc Hcb]
    as %mw ⟨%log, %rev, %crev, Htx, Htrc, ⟨%σ, HQ, %Hσ⟩⟩
  · iframe Hkvo Hs Hrd Htrc Hcb; ipureintro; exact Ht
  obtain ⟨hl, hc, hre⟩ := Hσ
  subst hl hc
  icases isTxnReadT_rev _ _ _ _ _ _ _ _ _ $$ Htx with ⟨Htx, %Hrev⟩
  subst Hrev
  (try wp_auto)
  ihave Htx : isTxnT mw st γ t (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
      iprop(True) $$ [Htx]
  · simp only [isTxnT]; iexact Htx
  wp_apply (hRev t mw st γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
      iprop(True)) $$ [$Htx] as Htx
  (try wp_auto)
  simp only [isTxnT, TxnKind.beginRev]
  ihave Hte : isTxnEndY mw st γ t (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
      iprop(True) iprop(True) $$ [Htx]
  · simp only [isTxnEndY]; iexact Htx
  ihave Hep : txnEndPreH γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) $$ []
  · simp only [txnEndPreH]; itrivial
  ihave Hx : txnEndX γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True) iprop(True)
      iprop(True) $$ []
  · simp only [txnEndX]; itrivial
  wp_apply (hEnd t mw st γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
      iprop(True) iprop(True) iprop(True) iprop(True)) $$ [$Hte $Hep $Hx]
    as ⟨Hrd, -, -, -, -⟩
  (try wp_auto)
  iunfold tokBack at Hback
  imod Hback $$ Hrd with Htok
  imodintro
  iapply HΦ
  iframe Htok
  iexists σ
  iframe HQ
  ipureintro; exact reach_rev hre

/-- **A read view's `FirstRev()`, by the caller's update** (see the header). -/
theorem readView_FirstRev_cb (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hFR : mvcc.metricsTxnWrite.FirstRev.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (st rv : Loc) (γ : StoreNames) (Q : MvccState → IProp GF) :
    {{ pkgInit ∗ isReadView rv st γ ∗ storeReaderC st γ ∗ tokBack st γ ∗ readAU γ Q }}
      (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"FirstRev")) (Val #()))
    {{ (r : w64), RET #r; threadTok ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 σ.crev⌝ }} := by
  wp_start as ⟨#Hrv, Hrd, Hback, Hau⟩
  iapply wp_fupd
  iunfold isReadView at Hrv
  icases Hrv with ⟨%kv, Hrv⟩
  iNamed Hrv
  ihave %Hkvok := kvOver_ok kv st $$ Hkvo
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  ihave Hcb := readCbC_of_au γ Q $$ Hau
  wp_apply (kvOver_ReadCb hRead kty kvv st γ _ t true
      (fun L c => iprop(∃ σ : MvccState, Q σ ∗ ⌜σ.log = L ∧ σ.crev = c ∧ MvccReachable σ⌝)))
      $$ [Hrd Htrc Hcb]
    as %mw ⟨%log, %rev, %crev, Htx, Htrc, ⟨%σ, HQ, %Hσ⟩⟩
  · iframe Hkvo Hs Hrd Htrc Hcb; ipureintro; exact Ht
  obtain ⟨hl, hc, hre⟩ := Hσ
  subst hl hc
  icases isTxnReadT_rev _ _ _ _ _ _ _ _ _ $$ Htx with ⟨Htx, %Hrev⟩
  subst Hrev
  (try wp_auto)
  wp_apply (hFR t mw st γ σ.log (W64 ((σ.log.length : Int) - 1)) σ.crev iprop(True) iprop(True))
    $$ [$Htx] as Htx
  (try wp_auto)
  ihave Hte : isTxnEndY mw st γ t (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
      iprop(True) iprop(True) $$ [Htx]
  · simp only [isTxnEndY]; iexact Htx
  ihave Hep : txnEndPreH γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) $$ []
  · simp only [txnEndPreH]; itrivial
  ihave Hx : txnEndX γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True) iprop(True)
      iprop(True) $$ []
  · simp only [txnEndX]; itrivial
  wp_apply (hEnd t mw st γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
      iprop(True) iprop(True) iprop(True) iprop(True)) $$ [$Hte $Hep $Hx]
    as ⟨Hrd, -, -, -, -⟩
  (try wp_auto)
  iunfold tokBack at Hback
  imod Hback $$ Hrd with Htok
  imodintro
  iapply HΦ
  iframe Htok
  iexists σ
  iframe HQ
  ipureintro; rfl

/-- **A read view's `Range()`, by the caller's update** (see the header). -/
theorem readView_Range_cb (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG))
    (hRangeW : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (st rv : Loc) (γ : StoreNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (todo : Bool) (key endk : GoSlice) (kk e : GoString) (ro : RangeOptions)
    (Q : MvccState → IProp GF) :
    {{ pkgInit ∗ isReadView rv st γ ∗ storeReaderC st γ ∗ tokBack st γ ∗ readAU γ Q ∗
        rangeCtx todo ctx cd ∗ key ↦*□ kk ∗ endk ↦*□ e }}
      (App (App (App (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Range"))
        (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
    {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); threadTok ∗ ⌜todo = true → r ≠ null⌝ ∗
        ∃ σ : MvccState, Q σ ∗
          rangeOutcomeC r err σ.log (W64 (σ.rev : Int)) σ.crev (decide (endk = slice.nil)) kk e ro ∗
          ⌜∀ r' : Nat, σ.crev ≤ (r' : Int) → r' ≤ σ.rev → stateOk (stateAt σ.log r')⌝ ∗
          ⌜LogWf' σ.log ∧ ∀ cs ∈ σ.log, cs.length < 2 ^ 63⌝ }} := by
  wp_start as ⟨#Hrv, Hrd, Hback, Hau, #Hctx, #Hkey, #Hend⟩
  iapply wp_fupd
  iunfold isReadView at Hrv
  icases Hrv with ⟨%kv, Hrv⟩
  iNamed Hrv
  ihave %Hkvok := kvOver_ok kv st $$ Hkvo
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  ihave Hcb := readCbC_of_au γ Q $$ Hau
  wp_apply (kvOver_ReadCb hRead kty kvv st γ _ t true
      (fun L c => iprop(∃ σ : MvccState, Q σ ∗ ⌜σ.log = L ∧ σ.crev = c ∧ MvccReachable σ⌝)))
      $$ [Hrd Htrc Hcb]
    as %mw ⟨%log, %rev, %crev, Htx, Htrc, ⟨%σ, HQ, %Hσ⟩⟩
  · iframe Hkvo Hs Hrd Htrc Hcb; ipureintro; exact Ht
  obtain ⟨hl, hc, hre⟩ := Hσ
  subst hl hc
  icases isTxnReadT_rev _ _ _ _ _ _ _ _ _ $$ Htx with ⟨Htx, %Hrev⟩
  subst Hrev
  ihave %Hsm := isTxnReadT_small _ _ _ _ _ _ _ _ _ $$ [$Htx]
  (try wp_auto)
  ihave Htx : isTxnT mw st γ t (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
      iprop(True) $$ [Htx]
  · simp only [isTxnT]; iexact Htx
  wp_apply (metricsTxnWrite_RangeT hRange hRangeW t mw st γ _ ctx cd todo key endk kk e ro σ.crev true)
      $$ [$Htx $Htrc $Hctx $Hkey $Hend] as %r %err ⟨%Htodo, Htx, Htrc, Hout⟩
  (try wp_auto)
  simp only [isTxnT, TxnKind.readLog, TxnKind.readRev]
  ihave Hte : isTxnEndY mw st γ t (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
      iprop(True) iprop(True) $$ [Htx]
  · simp only [isTxnEndY]; iexact Htx
  ihave Hep : txnEndPreH γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) $$ []
  · simp only [txnEndPreH]; itrivial
  ihave Hx : txnEndX γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True) iprop(True)
      iprop(True) $$ []
  · simp only [txnEndX]; itrivial
  wp_apply (hEnd t mw st γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
      iprop(True) iprop(True) iprop(True) iprop(True)) $$ [$Hte $Hep $Hx]
    as ⟨Hrd, -, -, -, -⟩
  (try wp_auto)
  iunfold tokBack at Hback
  imod Hback $$ Hrd with Htok
  imodintro
  iapply HΦ
  iframe Htok
  isplitr
  · ipureintro; exact Htodo
  iexists σ
  iframe HQ
  rw [← reach_rev hre]
  iframe Hout
  ipureintro
  exact ⟨fun r' _ _ => stateOk_at σ.log r' Hsm.1 Hsm.2.1 Hsm.2.2.2, Hsm.1, Hsm.2.2.1⟩

/-- The watchable handle's inner store's read view (`rv`, the one its field holds). -/
theorem watchable_view (s st : Loc) (γw : WsNames) :
    isWatchableStore (GF := GF) s st γw ⊢ ∀ rv : Loc,
      st.[store, go!"ReadView"] ↦□
        (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) -∗
      isReadView rv st γw.st := by
  iintro #Hws %rv' #Hrv'
  iunfold isWatchableStore at Hws
  iNamed Hws
  icombine Hrv Hrv' gives %Heq
  have h : rv = rv' := mkOk_loc_inj _ Heq
  subst h
  iunfold isReadView
  iexists (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s)
  iframe Hrvkv Hs
  iunfold kvOver
  iright
  iexists s
  iframe Hst
  ipureintro; rfl

/-- **`KV.Rev.contract` at `*watchableStore`.** -/
theorem watchableStore.Rev.wp_api (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    watchableStore.Rev.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) Q
  wp_start as ⟨Hmv, Htok, Hau⟩
  iunfold isMvcc at Hmv
  icases Hmv with #(Hmv | Hmv)
  · icases Hmv with ⟨Hmv, -⟩
    iunfold isMvccPlain at Hmv
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
  iNamed Hws'
  ihave #HrvI := watchable_view s st γw $$ Hws %rv Hrv
  wp_auto_lc 1
  iapply fupd_wp
  imod watchReader_borrow s st γw γp $$ [$Hlc1 $Hrp $Htok] with ⟨Hrd, Hback⟩
  imodintro
  iunfold mvccState at Hau
  wp_method_call; wp_call
  (try wp_auto)
  wp_apply (readView_Rev_cb hTODO hRead hRev hEnd st rv γw.st Q) $$ [$HrvI $Hrd $Hback $Hau]
    as %r Hr
  iapply HΦ; iexact Hr

/-- **`KV.FirstRev.contract` at `*watchableStore`.** -/
theorem watchableStore.FirstRev.wp_api (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hFR : mvcc.metricsTxnWrite.FirstRev.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    watchableStore.FirstRev.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) Q
  wp_start as ⟨Hmv, Htok, Hau⟩
  iunfold isMvcc at Hmv
  icases Hmv with #(Hmv | Hmv)
  · icases Hmv with ⟨Hmv, -⟩
    iunfold isMvccPlain at Hmv
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
  iNamed Hws'
  ihave #HrvI := watchable_view s st γw $$ Hws %rv Hrv
  wp_auto_lc 1
  iapply fupd_wp
  imod watchReader_borrow s st γw γp $$ [$Hlc1 $Hrp $Htok] with ⟨Hrd, Hback⟩
  imodintro
  iunfold mvccState at Hau
  wp_method_call; wp_call
  (try wp_auto)
  wp_apply (readView_FirstRev_cb hTODO hRead hFR hEnd st rv γw.st Q) $$ [$HrvI $Hrd $Hback $Hau]
    as %r Hr
  iapply HΦ; iexact Hr

/-- **`KV.Range.contract` at `*watchableStore`.** -/
theorem watchableStore.Range.wp_api (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG))
    (hRangeW : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    watchableStore.Range.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) ctx cd todo key endk kk e ro Q
  wp_start as ⟨Hmv, Htok, #Hctx, #Hkey, #Hend, Hau⟩
  iunfold isMvcc at Hmv
  icases Hmv with #(Hmv | Hmv)
  · icases Hmv with ⟨Hmv, -⟩
    iunfold isMvccPlain at Hmv
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
  iNamed Hws'
  ihave #HrvI := watchable_view s st γw $$ Hws %rv Hrv
  wp_auto_lc 1
  iapply fupd_wp
  imod watchReader_borrow s st γw γp $$ [$Hlc1 $Hrp $Htok] with ⟨Hrd, Hback⟩
  imodintro
  iunfold mvccState at Hau
  wp_method_call; wp_call
  (try wp_auto)
  wp_apply (readView_Range_cb hTODO hRead hRange hRangeW hEnd st rv γw.st ctx cd todo key endk kk e ro
      Q) $$ [$HrvI $Hrd $Hback $Hau $Hctx $Hkey $Hend]
    as %r %err Hr
  iapply HΦ; iexact Hr

end proof

end api
end mvcc
end EtcdGrove
end Perennial
