/-
Proof of the spec of the same name (the watch slice's unit W-S): the send loop. The order of the
mvcc responses it sends is `WatchSendModel`'s (`SendInv`, `send_claim_direct`,
`send_claim_flush`). Lean-first (no Rocq counterpart). Over mvcc's API (2026-11-05): the stream's
`Chan` and `RequestProgress` contracts through `shapes.law`, its channel's receives
(`wsChan_recv.law`: `WatchApi.drain_poll`, `wp_ws_receive`), the snapshot after each receipt
(`WatchApi.snap_after_recv`), the drain to a created response's watcher's stamp (`wsSentLb`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__sendLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__newResponseHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.GetProgressReportInterval
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isClientCtxErr
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Assert
public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.Ticker__Stop
public import Spec.time.Duration__Seconds
public import Spec.time.Duration__Seconds_ptr
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchSendModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchSendPure

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- An mvcc response's message reads the same at any source index (`watchRespMsg` reads the wire's
fields only). -/
theorem v3rpc.watchRespMsg_mvccResp (l : Loc) (n n' : Nat) (x : mvcc.api.WResp) (h : HdrM) :
    v3rpc.watchRespMsg (GF := GF) l (v3rpc.mvccResp n x h) ⊢
      v3rpc.watchRespMsg l (v3rpc.mvccResp n' x h) := by
  unfold v3rpc.watchRespMsg v3rpc.mvccResp
  iintro H; iexact H

/-- **A slice of buffered responses** (persistent): `sl` holds the responses `ls`, the `i`th the
response the send loop made of the mvcc response at index `P[i]` of those received `rcv` (with the
server's header, its revision the response's; its message at the source index `0`, which the wire
does not carry: `watchRespMsg_mvccResp`). -/
def v3rpc.pendSl (r : v3rpc.WRun GF) (rcv : List mvcc.api.WResp) (P : List Nat) (sl : GoSlice) :
    IProp GF :=
  iprop(∃ (ls : List Loc) (xs : List (mvcc.api.WResp × HdrM)), sl ↦*□ ls ∗
    ⌜ls.length = xs.length ∧ P.map (fun n => rcv[n]?) = xs.map (fun p => some p.1) ∧
      ∀ p ∈ xs, p.2.clusterId = r.srv.cid ∧ p.2.memberId = r.srv.mid ∧ p.2.revision = p.1.rev⌝ ∗
    [∗list] q ∈ ls.zip xs, v3rpc.watchRespMsg q.1 (v3rpc.mvccResp 0 q.2.1 q.2.2))

instance v3rpc.pendSl_persistent (r : v3rpc.WRun GF) (rcv : List mvcc.api.WResp) (P : List Nat)
    (sl : GoSlice) : Persistent (v3rpc.pendSl r rcv P sl) := by
  unfold v3rpc.pendSl; infer_instance

/-- **What the send loop knows of the responses it received** (persistent): for each, the received
list's lower bound and the snapshot (`snap_after_recv`) up to it. -/
def v3rpc.rcvOk (r : v3rpc.WRun GF) (rcv : List mvcc.api.WResp) : IProp GF :=
  iprop(□ ∀ (n : Nat) (x : mvcc.api.WResp), ⌜rcv[n]? = some x⌝ -∗
    v3rpc.rcvLb r.γr (rcv.take (n + 1)) ∗
    ∃ (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState), □ v3rpc.rcvSnap r (rcv.take (n + 1)) σ S)

instance v3rpc.rcvOk_persistent (r : v3rpc.WRun GF) (rcv : List mvcc.api.WResp) :
    Persistent (v3rpc.rcvOk r rcv) := by
  unfold v3rpc.rcvOk; infer_instance

/-- **The send loop's state** of the mvcc responses `rcv` received with the responses `D` sent:
`WatchSendModel`'s invariant (`SendInv`) over the indices `S` sent and `pend` buffered, the ids
announced `IM` (the map `ids`), the mvcc responses sent being those of `S` in order (`srcOf`), the
buffered responses (the map `pending`, `PM`); an id other than `-1` is announced exactly when it is
live after the responses sent (`idLive`); the history of the sends (`SendHist`); the registry
entries `M` of the announced ids (from their created responses, `ctrlWatcher`; for the
snapshot after a receipt, `snap_after_recv`); what it knows of the responses received. -/
def v3rpc.sendSt (r : v3rpc.WRun GF) (idsL pendL : Loc) (rcv : List mvcc.api.WResp)
    (D : List v3rpc.WatchRespM) : IProp GF :=
  iprop(∃ (S : List Nat) (pend : w64 → List Nat) (IM : GMap w64 Unit) (PM : GMap w64 GoSlice)
      (M : GMap w64 v3rpc.RegInfo),
    ⌜v3rpc.SendInv rcv S pend (fun X => (IM !! X).isSome) none ∧
      D.filterMap v3rpc.WatchRespM.src = v3rpc.srcOf rcv S ∧
      (∀ X, PM !! X = none → pend X = []) ∧
      (∀ X, X ≠ W64 (-1) → ((IM !! X).isSome = true ↔ v3rpc.idLive D X)) ∧
      v3rpc.SendHist rcv D S ∧
      (∀ X, X ≠ W64 (-1) → (IM !! X).isSome = true → (M !! X).isSome = true)⌝ ∗
    ownMap idsL (DFrac.own 1) IM ∗ ownMap pendL (DFrac.own 1) PM ∗
    ([∗map] _X ↦ sl ∈ PM, ownSliceCap Loc sl (DFrac.own 1)) ∗
    ([∗map] X ↦ sl ∈ PM, v3rpc.pendSl r rcv (pend X) sl) ∗
    □ ([∗map] X ↦ i ∈ M, v3rpc.regIs r.γreg X i) ∗
    v3rpc.rcvOk r rcv)

/-! ## The receipts -/

open Iris.ProofMode in
/-- A receipt: the received list's lower bound and the snapshot at it extend `rcvOk`. -/
theorem v3rpc.rcvOk_snoc (r : v3rpc.WRun GF) (rcv : List mvcc.api.WResp) (x : mvcc.api.WResp)
    (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState) :
    v3rpc.rcvOk (GF := GF) r rcv ∗ v3rpc.rcvLb r.γr (rcv ++ [x]) ∗
      □ v3rpc.rcvSnap r (rcv ++ [x]) σ S ⊢ v3rpc.rcvOk r (rcv ++ [x]) := by
  iintro ⟨#H, #Hl, #Hs⟩
  iunfold v3rpc.rcvOk at H
  iunfold v3rpc.rcvOk
  iintro !> %n %y %hy
  rcases Nat.lt_or_ge n rcv.length with hl | hl
  · rw [List.getElem?_append_left hl] at hy
    rw [List.take_append_of_le_length (show n + 1 ≤ rcv.length by omega)]
    iapply H $$ %n %y %hy
  · have hn : n = rcv.length := by
      rcases Nat.lt_or_ge n (rcv.length + 1) with h' | h'
      · omega
      · rw [List.getElem?_eq_none (by simp; omega)] at hy; cases hy
    subst hn
    rw [show rcv.length + 1 = (rcv ++ [x]).length by simp, List.take_length]
    iframe Hl
    iexists σ, S
    iexact Hs

/-- Buffered responses read the same after a receipt. -/
theorem v3rpc.pendSl_snoc (r : v3rpc.WRun GF) (rcv : List mvcc.api.WResp) (x : mvcc.api.WResp)
    (P : List Nat) (sl : GoSlice) :
    v3rpc.pendSl r rcv P sl ⊢ v3rpc.pendSl r (rcv ++ [x]) P sl := by
  iintro H
  iunfold v3rpc.pendSl at H
  iunfold v3rpc.pendSl
  icases H with ⟨%ls, %xs, #Hls, %Hp, #Hm⟩
  iexists ls, xs
  iframe Hls Hm
  ipureintro
  exact ⟨Hp.1, v3rpc.map_snoc_some rcv x P xs Prod.fst Hp.2.1, Hp.2.2⟩

/-- The buffer maps after `delete(pending, X)` (its responses all sent): `X`'s slice and its
capacity dropped, `X` with nothing buffered. -/
theorem v3rpc.pendMaps_delete (r : v3rpc.WRun GF) (rcv : List mvcc.api.WResp) (pend : w64 → List Nat)
    (PM : GMap w64 GoSlice) (X : w64) :
    ([∗map] _Y ↦ sl ∈ PM, ownSliceCap Loc sl (DFrac.own 1)) ∗
      ([∗map] Y ↦ sl ∈ PM, v3rpc.pendSl r rcv (pend Y) sl) ⊢
    ([∗map] _Y ↦ sl ∈ GMap.delete X PM, ownSliceCap Loc sl (DFrac.own 1)) ∗
      ([∗map] Y ↦ sl ∈ GMap.delete X PM, v3rpc.pendSl r rcv (v3rpc.upd pend X [] Y) sl) := by
  have hmono : ([∗map] Y ↦ sl ∈ GMap.delete X PM, v3rpc.pendSl (GF := GF) r rcv (pend Y) sl) ⊢
      [∗map] Y ↦ sl ∈ GMap.delete X PM, v3rpc.pendSl r rcv (v3rpc.upd pend X [] Y) sl :=
    BigSepM.bigSepM_mono fun {k v} hk => by
      have hne : k ≠ X := by
        intro h; subst h
        have := GMap.lookup_delete PM k
        have hk' : (GMap.delete k PM) !! k = some v := hk
        rw [this] at hk'; cases hk'
      rw [v3rpc.upd_ne _ _ hne]
  cases hX : PM !! X with
  | none =>
    have he : GMap.delete X PM = PM := GMap.map_eq fun k => by
      by_cases h : k = X
      · subst h; rw [GMap.lookup_delete, hX]
      · rw [GMap.lookup_delete_ne _ (Ne.symm h)]
    iintro ⟨Hc, Hp⟩
    ihave Hp' := hmono $$ [Hp]
    · rw [he]; iexact Hp
    rw [he]
    iframe Hc Hp'
  | some sl =>
    iintro ⟨Hc, Hp⟩
    icases (BigSepM.bigSepM_delete hX).1 $$ Hc with ⟨-, Hc⟩
    icases (BigSepM.bigSepM_delete hX).1 $$ Hp with ⟨-, Hp⟩
    iframe Hc
    iapply hmono $$ Hp

/-- `pending[X]`'s capacity taken out (the nil slice's, if `X` has none). -/
theorem v3rpc.pendCaps_take (PM : GMap w64 GoSlice) (X : w64) :
    ([∗map] _Y ↦ sl ∈ PM, ownSliceCap (GF := GF) Loc sl (DFrac.own 1)) ⊢
      ownSliceCap Loc ((PM !! X).getD (zero_val GoSlice)) (DFrac.own 1) ∗
      ([∗map] _Y ↦ sl ∈ GMap.delete X PM, ownSliceCap Loc sl (DFrac.own 1)) := by
  cases hX : PM !! X with
  | none =>
    have he : GMap.delete X PM = PM := GMap.map_eq fun k => by
      by_cases h : k = X
      · subst h; rw [GMap.lookup_delete, hX]
      · rw [GMap.lookup_delete_ne _ (Ne.symm h)]
    rw [he]
    iintro Hc
    iframe Hc
    simp only [Option.getD_none]
    iapply (ownSliceCap_nil (V := Loc))
  | some sl =>
    iintro Hc
    icases (BigSepM.bigSepM_delete hX).1 $$ Hc with ⟨H1, Hc⟩
    simp only [Option.getD_some]
    isplitl [H1]
    · iexact H1
    iexact Hc

/-- `pending[X] = sl'`: the capacities and the buffered slices, `X`'s now `P'`. -/
theorem v3rpc.pendMaps_insert (r : v3rpc.WRun GF) (rcv : List mvcc.api.WResp) (pend : w64 → List Nat)
    (PM : GMap w64 GoSlice) (X : w64) (sl' : GoSlice) (P' : List Nat) :
    ([∗map] _Y ↦ sl ∈ GMap.delete X PM, ownSliceCap Loc sl (DFrac.own 1)) ∗
      ([∗map] Y ↦ sl ∈ PM, v3rpc.pendSl r rcv (pend Y) sl) ∗
      ownSliceCap Loc sl' (DFrac.own 1) ∗ v3rpc.pendSl r rcv P' sl' ⊢
    ([∗map] _Y ↦ sl ∈ <[X := sl']> PM, ownSliceCap Loc sl (DFrac.own 1)) ∗
      ([∗map] Y ↦ sl ∈ <[X := sl']> PM, v3rpc.pendSl r rcv (v3rpc.upd pend X P' Y) sl) := by
  iintro ⟨Hc, Hp, Hc', Hp'⟩
  isplitl [Hc Hc']
  · iapply (BigSepM.bigSepM_insert_delete (m := PM) (i := X) (x := sl')
      (Φ := fun _ sl => ownSliceCap (GF := GF) Loc sl (DFrac.own 1))).2
    iframe Hc Hc'
  iapply (BigSepM.bigSepM_insert_delete (m := PM) (i := X) (x := sl')
    (Φ := fun Y sl => v3rpc.pendSl (GF := GF) r rcv (v3rpc.upd pend X P' Y) sl)).2
  isplitl [Hp']
  · rw [v3rpc.upd_same]; iexact Hp'
  have hmono : ([∗map] Y ↦ sl ∈ GMap.delete X PM, v3rpc.pendSl (GF := GF) r rcv (pend Y) sl) ⊢
      [∗map] Y ↦ sl ∈ GMap.delete X PM, v3rpc.pendSl r rcv (v3rpc.upd pend X P' Y) sl :=
    BigSepM.bigSepM_mono fun {k v} hk => by
      have hne : k ≠ X := by
        intro h; subst h
        have := GMap.lookup_delete PM k
        have hk' : (GMap.delete k PM) !! k = some v := hk
        rw [this] at hk'; cases hk'
      rw [v3rpc.upd_ne _ _ hne]
  iapply hmono
  cases hX : PM !! X with
  | none =>
    have he : GMap.delete X PM = PM := GMap.map_eq fun k => by
      by_cases h : k = X
      · subst h; rw [GMap.lookup_delete, hX]
      · rw [GMap.lookup_delete_ne _ (Ne.symm h)]
    rw [he]; iexact Hp
  | some sl =>
    icases (BigSepM.bigSepM_delete hX).1 $$ Hp with ⟨-, Hp⟩
    iexact Hp

/-- A receipt: the buffered slices read the same. -/
theorem v3rpc.pendSls_snoc (r : v3rpc.WRun GF) (rcv : List mvcc.api.WResp) (x : mvcc.api.WResp)
    (pend : w64 → List Nat) (PM : GMap w64 GoSlice) :
    ([∗map] Y ↦ sl ∈ PM, v3rpc.pendSl (GF := GF) r rcv (pend Y) sl) ⊢
      [∗map] Y ↦ sl ∈ PM, v3rpc.pendSl r (rcv ++ [x]) (pend Y) sl :=
  BigSepM.bigSepM_mono fun {_ _} _ => v3rpc.pendSl_snoc r rcv x _ _

open Iris.ProofMode in
/-- **Every received response of id `-1` was sent** (unit W-K), from the send state. -/
theorem v3rpc.sendSt_neg1 (r : v3rpc.WRun GF) (idsL pendL : Loc) (rcv : List mvcc.api.WResp)
    (D : List v3rpc.WatchRespM) :
    v3rpc.sendSt r idsL pendL rcv D ⊢ ⌜∀ (n : Nat) (x : mvcc.api.WResp), rcv[n]? = some x →
      x.id = W64 (-1) → ∃ m' ∈ D, m'.src = some (n, x)⌝ := by
  iintro HS
  iunfold v3rpc.sendSt at HS
  icases HS with ⟨%S, %pend, %IM, %PM, %M, %HSI, -, -, -, -, -, -⟩
  obtain ⟨hI, hD, -, -, -, -⟩ := HSI
  ipureintro; exact v3rpc.neg1_sent hI hD

/-! ## The proof's program points

The proof below is split at three program points, so that the code after each is elaborated
once: the `sendWatch` closure (its spec, `HsW`, proved once before the loop and used by the loop's
`watchStream.Chan()` case and by the drain before a created response), the loop's `return`
(the loop's postcondition `sendRet`, from which the deferred function runs once) and the end of
the control case's `if c.Created` (`ctrlMid`, after which the rest of the control case runs
once). -/

/-- **The send loop's thread resources**: its thread token and (the store's readers as client-held
tokens, 2026-11-07) a reader token of the store, which `RequestProgress` takes. -/
abbrev v3rpc.sendTok (r : v3rpc.WRun GF) : IProp GF :=
  iprop(threadTok ∗ mvcc.api.mvccReaders r.W.γm 1)

/-- **What the send loop's return needs** (the deferred function, `send_return`): the mvcc
channel's consumer (`wsRecv`), the loop's thread token, and the buffered responses (`pending`,
with `sendSt`'s slices). -/
def v3rpc.retSt (r : v3rpc.WRun GF) (pendL : Loc) : IProp GF :=
  iprop(∃ (rcvc rcv : List mvcc.api.WResp) (pend : w64 → List Nat) (PM : GMap w64 GoSlice),
    mvcc.api.wsRecv r.ι rcvc ∗ v3rpc.sendTok r ∗ ownMap pendL (DFrac.own 1) PM ∗
    [∗map] X ↦ sl ∈ PM, v3rpc.pendSl r rcv (pend X) sl)

theorem v3rpc.retSt_intro (r : v3rpc.WRun GF) (pendL : Loc) (rcvc rcv : List mvcc.api.WResp)
    (pend : w64 → List Nat) (PM : GMap w64 GoSlice) :
    mvcc.api.wsRecv r.ι rcvc ∗ v3rpc.sendTok r ∗ ownMap pendL (DFrac.own 1) PM ∗
      ([∗map] X ↦ sl ∈ PM, v3rpc.pendSl r rcv (pend X) sl) ⊢ v3rpc.retSt r pendL := by
  iintro ⟨Hwc, Htt, HPM, Hpsl⟩
  iunfold v3rpc.retSt
  iexists rcvc, rcv, pend, PM
  iframe

theorem v3rpc.retSt_of_sendSt (r : v3rpc.WRun GF) (idsL pendL : Loc) (rcvc rcv : List mvcc.api.WResp)
    (D : List v3rpc.WatchRespM) :
    mvcc.api.wsRecv r.ι rcvc ∗ v3rpc.sendTok r ∗ v3rpc.sendSt r idsL pendL rcv D ⊢
      v3rpc.retSt r pendL := by
  iintro ⟨Hwc, Htt, HS⟩
  iunfold v3rpc.sendSt at HS
  icases HS with ⟨%S, %pend, %IM, %PM, %M, -, -, HPM, -, #Hpsl, -⟩
  iapply (v3rpc.retSt_intro r pendL rcvc rcv pend PM)
  iframe Hwc Htt HPM
  iexact Hpsl

/-- **The send loop's postcondition**: it returns (every exit of the loop is a `return`), with
what the deferred function needs (`retSt`). -/
def v3rpc.sendRet (r : v3rpc.WRun GF) (pendL : Loc) (v : val) : IProp GF :=
  iprop(⌜v = returnVal #()⌝ ∗ v3rpc.retSt r pendL)

theorem v3rpc.sendRet_intro (r : v3rpc.WRun GF) (pendL : Loc) :
    v3rpc.retSt r pendL ⊢ v3rpc.sendRet r pendL (returnVal #()) := by
  iintro H
  iunfold v3rpc.sendRet
  iframe H
  ipureintro; rfl

/-- **After the control case's `if c.Created`** (the drain before a created response, unit W-K,
or nothing): the send loop's state, the created response's watcher and its `createdAfter`, for
the rest of the control case; or (a failed send in the drain) the return. -/
def v3rpc.ctrlMid (r : v3rpc.WRun GF) (ci : GoInterfaceOk) (sws idsL pendL : Loc)
    (req : v3rpc.WatchReqM) (m : v3rpc.WatchRespM) (v : val) : IProp GF :=
  iprop((⌜v = executeVal⌝ ∗ ∃ (rcv : List mvcc.api.WResp) (D : List v3rpc.WatchRespM),
      v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs D ∗ mvcc.api.wsRecv r.ι rcv ∗
      monoListAuthOwn r.γr 1 rcv ∗ v3rpc.sendTok r ∗ v3rpc.sendSt r idsL pendL rcv D ∗
      sync.ownRWMutex (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) ∗
      v3rpc.ctrlWatcher r (auth.ctxTokenOf (GoInterface.ok ci)) req m ∗
      v3rpc.createdAfter r D.length m) ∨
    (⌜v = returnVal #()⌝ ∗ v3rpc.retSt r pendL))

theorem v3rpc.ctrlMid_exec (r : v3rpc.WRun GF) (ci : GoInterfaceOk) (sws idsL pendL : Loc)
    (req : v3rpc.WatchReqM) (m : v3rpc.WatchRespM) (rcv : List mvcc.api.WResp)
    (D : List v3rpc.WatchRespM) :
    v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs D ∗ mvcc.api.wsRecv r.ι rcv ∗
      monoListAuthOwn r.γr 1 rcv ∗ v3rpc.sendTok r ∗ v3rpc.sendSt r idsL pendL rcv D ∗
      sync.ownRWMutex (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) ∗
      v3rpc.ctrlWatcher r (auth.ctxTokenOf (GoInterface.ok ci)) req m ∗
      v3rpc.createdAfter r D.length m ⊢
    v3rpc.ctrlMid r ci sws idsL pendL req m executeVal := by
  iintro H
  iunfold v3rpc.ctrlMid
  ileft
  isplitr
  · ipureintro; rfl
  iexists rcv, D
  iexact H

theorem v3rpc.ctrlMid_ret (r : v3rpc.WRun GF) (ci : GoInterfaceOk) (sws idsL pendL : Loc)
    (req : v3rpc.WatchReqM) (m : v3rpc.WatchRespM) :
    v3rpc.retSt r pendL ⊢ v3rpc.ctrlMid r ci sws idsL pendL req m (returnVal #()) := by
  iintro H
  iunfold v3rpc.ctrlMid
  iright
  iframe H
  ipureintro; rfl

open Iris.ProofMode in
/-- **A registered watcher's entry and stamp**, out of its created response's `ctrlWatcher` (both
persistent, `persistent.law`), the `ctrlWatcher` kept. -/
theorem v3rpc.ctrlWatcher_reg (hP : mvcc.api.persistent.law (GF := GF)) (r : v3rpc.WRun GF)
    (tok : Option GoString) (c : v3rpc.CreateReqM) (m : v3rpc.WatchRespM)
    (h : m.canceled = false) :
    v3rpc.ctrlWatcher (GF := GF) r tok (.create c) m ⊢
      v3rpc.ctrlWatcher r tok (.create c) m ∗
        ∃ i : v3rpc.RegInfo, v3rpc.regIs r.γreg m.watchId i ∗ mvcc.api.wsSentLb r.ι i.k := by
  have : ∀ ι n, Persistent (mvcc.api.wsSentLb (GF := GF) ι n) := hP.2.2.1
  unfold v3rpc.ctrlWatcher
  rw [h]
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro ⟨%i, %Hrg, #Hreg, Htok, #Hk, Hlo, Hau⟩
  isplitl [Htok Hlo Hau]
  · iexists i
    iframe Htok Hlo Hau Hreg Hk
    ipureintro; exact Hrg
  iexists i
  iframe Hreg Hk

open Iris.ProofMode in
/-- **The registry entries of the announced ids, after a created response for `X` is sent**: the
created response's entry (`createdAfter`'s) joins them, unless the create was refused (then `X` is
`-1`, which needs none). -/
theorem v3rpc.regMap_created (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) (X : w64)
    (IM : GMap w64 Unit) (M : GMap w64 v3rpc.RegInfo) (hX : m.watchId = X)
    (hcr : m.created = true) (hcc : m.canceled = true → X = W64 (-1))
    (hMI : ∀ Y, Y ≠ W64 (-1) → (IM !! Y).isSome = true → (M !! Y).isSome = true) :
    □ ([∗map] Y ↦ i ∈ M, v3rpc.regIs (GF := GF) r.γreg Y i) ∗ v3rpc.createdAfter r j m ⊢
      ∃ M' : GMap w64 v3rpc.RegInfo, □ ([∗map] Y ↦ i ∈ M', v3rpc.regIs r.γreg Y i) ∗
        ⌜∀ Y, Y ≠ W64 (-1) → ((<[X := ()]> IM) !! Y).isSome = true → (M' !! Y).isSome = true⌝ := by
  cases hca : m.canceled
  · unfold v3rpc.createdAfter
    rw [hcr, hca]
    simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
    iintro ⟨#HM, #Hord⟩
    icases Hord with ⟨%i, %l, %L, #Hreg, -⟩
    iexists <[X := i]> M
    isplitr
    · iintro !>
      iapply BigSepM.bigSepM_intro (P := iprop(□ (v3rpc.regIs (GF := GF) r.γreg X i ∗
          [∗map] Y ↦ i ∈ M, v3rpc.regIs r.γreg Y i)))
        (Φ := fun Y i => v3rpc.regIs (GF := GF) r.γreg Y i) (m := <[X := i]> M)
        (fun {k v} hk => by
          by_cases hkX : k = X
          · subst hkX
            have : v = i := by
              have := hk
              rw [show Std.get? (<[k := i]> M) k = (<[k := i]> M) !! k from rfl,
                GMap.lookup_insert] at this
              exact (Option.some.inj this).symm
            subst this
            iintro #⟨H1, -⟩; iexact H1
          · have hk' : Std.get? M k = some v := by
              have := hk
              rw [show Std.get? (<[X := i]> M) k = (<[X := i]> M) !! k from rfl,
                GMap.lookup_insert_ne _ _ (Ne.symm hkX)] at this
              exact this
            iintro #⟨-, H2⟩
            iapply BigSepM.bigSepM_lookup (Φ := fun Y i => v3rpc.regIs (GF := GF) r.γreg Y i) hk'
              $$ H2)
      iintro !>
      rw [← hX]
      iframe Hreg HM
    · ipureintro
      intro Y hY hI
      by_cases h : Y = X
      · subst h; simp [GMap.lookup_insert]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]
        rw [GMap.lookup_insert_ne _ _ (Ne.symm h)] at hI
        exact hMI Y hY hI
  · iintro ⟨#HM, -⟩
    iexists M
    iframe HM
    ipureintro
    intro Y hY hI
    have hX1 := hcc hca
    have h : Y ≠ X := by rw [hX1]; exact hY
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h)] at hI
    exact hMI Y hY hI

end defs

set_option hygiene false in
/-- **The send loop's return** (the loop's postcondition `sendRet`, once for every `return` of
the loop): the deferred function stops the ticker, drains the mvcc stream's channel
(`wsRecv`) and reports the buffered responses (`pending`, from `retSt`). -/
local macro "send_return" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hStop tk $$ []
  · iexact Htk
  wp_apply (hCh r.W.γm r.ι) $$ [] as %ch' %Hch'
  · iframe #
  subst Hch'
  (try wp_auto)
  ihave Hdr : iprop(∃ (rcv' : List mvcc.api.WResp) (v : go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse),
      "Hwc" ∷ mvcc.api.wsRecv r.ι rcv' ∗ "ws" ∷ ws_ptr ↦ v) $$ [Hwc ws]
  · iexists _, _; iframe
  wp_for Hdr
  (try simp only [_root_.decide_true, ↓reduceIte])
  (try wp_auto)
  wp_apply v3rpc.wp_ws_receive hR (interface.mkOk wsty wsv) r.W.γm r.ι rcv' $$ Hwstream Hwc
  iintro %wv %okw Hres
  cases okw
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_for_post
    try iunfold v3rpc.sendSt at HS
    try icases HS with ⟨%S, %pend, %IM, %PM, %M, %HSI, HIM, HPM, Hcaps, #Hpsl, #HM, #Hrok⟩
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun _ _ => iprop(∃ v : GoSlice, "wrs" ∷ wrs_ptr ↦ v)) _ _ _ pendL PM
      (DFrac.own 1) $$ HPM
    iintro %keys %Hkeys
    isplitl [wrs]
    · iexists _; iexact wrs
    isplitr
    · iintro !> %i %X %sl ⟨%Hk, %Hsl⟩ Hw
      icases Hw with ⟨%v0, wrs⟩
      ihave #Hp := BigSepM.bigSepM_lookup (Φ := fun X sl => v3rpc.pendSl r rcv (pend X) sl) Hsl $$ Hpsl
      iunfold v3rpc.pendSl at Hp
      icases Hp with ⟨%ls, %xs, #Hls, %Hxs, #Hmsgs⟩
      wp_auto
      ihave %Hlsl := ownSlice_len _ _ _ $$ Hls
      ihave HI : iprop(∃ (j : w64) (v : Loc), "i" ∷ i_ptr ↦ j ∗ "ws" ∷ ws_ptr ↦ v ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j⌝) $$ [i ws]
      · iexists _, _; iframe; ipureintro; decide
      wp_for HI
      wp_if_destruct
      · have Hif' : sint.Z j < sint.Z sl.len := by
          first
          | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
          | exact Hif
        have Hlen1 := Hlsl.1
        obtain ⟨l, hl⟩ : ∃ l, ls[(sint.Z j).toNat]? = some l :=
          ⟨_, List.getElem?_eq_getElem (by word)⟩
        obtain ⟨xp, hxp⟩ : ∃ xp, xs[(sint.Z j).toNat]? = some xp :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hxs.1]; word)⟩
        have hz : (ls.zip xs)[(sint.Z j).toNat]? = some (l, xp) := by
          rw [List.getElem?_zip_eq_some]; exact ⟨hl, hxp⟩
        ihave #Hm := BigSepL.bigSepL_lookup
          (Φ := fun _ q => v3rpc.watchRespMsg (GF := GF) q.1 (v3rpc.mvccResp 0 q.2.1 q.2.2)) hz $$ Hmsgs
        iunfold v3rpc.watchRespMsg at Hm
        icases Hm with ⟨%Hln, %h, %esl, %eps, -, -, -, -, -, -, -, -, #HEv, #HEsl, -⟩
        ihave %HEsl' := ownSlice_len _ _ _ $$ HEsl
        have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj, Hif'⟩
        simp only [Hbnd, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index sl (sint.Z j) ls DFrac.discard l Hj $$ [] as -
        · iframe Hls; ipureintro; exact hl
        wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) _)
        iapply Hrep
        · ipureintro; first | exact HEsl'.2 | omega | word
        iintro !> -
        wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; word
      · (try (have Hf : (#(decide (sint.Z j < sint.Z sl.len)) : val) = #false := by
                revert Hif; cases decide (sint.Z j < sint.Z sl.len) <;> intro Hif
                · rfl
                · exact absurd rfl Hif
              rw [show decide ((#(decide (sint.Z j < sint.Z sl.len)) : val) = #false) = true from
                decide_eq_true Hf]
              simp only [↓reduceIte]))
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _; iexact wrs
    iintro - HPM
    wp_auto
    iapply HΦ
    iexact Htt
  simp only [↓reduceIte]
  icases Hres with ⟨%x, Hwc, #HrIR⟩
  iunfold mvcc.api.wrespIs at HrIR
  icases HrIR with ⟨-, %psR, #HpsR, -⟩
  ihave %HlR := ownSlice_len _ _ _ $$ HpsR
  wp_auto
  wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) _)
  iapply Hrep
  · ipureintro; first | exact HlR.2 | omega | word
  iintro !> -
  wp_auto
  wp_for_post
  iframe
  iexists _, _
  iframe))

set_option hygiene false in
/-- `h.Observe(x)` of a histogram whose `Observe` returns (`Ho`). -/
local macro "observe" h:term:max Ho:ident : tactic => `(tactic| (
  wp_bind (App (Val #(methods ($h).ty go!"Observe" ($h).v)) _)
  iapply $Ho:ident
  · itrivial
  iintro !> -))

set_option hygiene false in
/-- `retSt` from the context: `Hret`, or the consumer `Hwc`, the thread token `Htt` and the send
state `HS` (whole, or its buffer map `HPM` and slices `Hpsl`). -/
local macro "ret_frame" : tactic => `(tactic| (
  first
  | iexact Hret
  | (iapply (v3rpc.retSt_of_sendSt _ _ _ _ _ _)
     isplitl [Hwc]
     · iexact Hwc
     isplitl [Htt]
     · iexact Htt
     iexact HS)
  | (iapply (v3rpc.retSt_intro _ _ _ _ _ _)
     isplitl [Hwc]
     · iexact Hwc
     isplitl [Htt]
     · iexact Htt
     isplitl [HPM]
     · iexact HPM
     iexact Hpsl)))

set_option hygiene false in
/-- **A `return` of the loop** (from its body, or a loop inside it): its postcondition
`sendRet` (the deferred function runs after the loop, `send_return`). -/
local macro "ret_exit" : tactic => `(tactic| (
  wp_for_post
  (try wp_auto)
  (try wp_for_post)
  iapply v3rpc.sendRet_intro
  ret_frame))

set_option hygiene false in
/-- **A `return` inside the control case's `if c.Created`** (the drain's): `ctrlMid`'s return. -/
local macro "ret_mid" : tactic => `(tactic| (
  wp_for_post
  (try wp_auto)
  iapply v3rpc.ctrlMid_ret
  ret_frame))

set_option hygiene false in
/-- **A failed send** (`serr != nil`, from `Send`'s error case `Hne`): the context's error and
`isClientCtxErr` choose the log, then the loop returns (`k`: `ret_exit`, or the `sendWatch`
closure's `false`). -/
local macro "send_fail" k:tactic : tactic => `(tactic| (
  rcases serr with ei | _
  rotate_left
  · exact absurd rfl Hne
  wp_auto
  (try rw [Hsi])
  (try wp_auto)
  wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
  iapply HCtx
  · itrivial
  iintro !> -
  wp_auto
  wp_apply +noauto HErrU $$ [] as %cerr - -
  wp_auto
  wp_apply hICE as %bc -
  wp_if_destruct
  · wp_apply hZE as %f -
    wp_apply wp_slice_literal (l := [f])
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hZW r.srv.lg _ _ $$ []
    · iframe #; ipureintro; exact Hnn.2
    wp_apply wp_slice_literal (V := GoString) [go!"send", go!"watch"]
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_auto
    wp_apply hCV cvF _ [go!"Type", go!"API"] _ _ $$ [Hlsl] as %cnt ⟨%cnti, %Hcnt, #Hcs, -⟩
    · iframe #; iframe Hlsl; ipureintro
      exact ⟨HcvFl, prometheus.labelValuesOk_two _ _ _ _ (by decide) (by decide)⟩
    subst Hcnt
    iunfold prometheus.counterSpec at Hcs
    icases Hcs with ⟨#Hcs, -⟩
    wp_apply Hcs
    (try wp_auto)
    $k
  · wp_apply hZE as %f -
    wp_apply wp_slice_literal (l := [f])
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hZD r.srv.lg _ _ $$ []
    · iframe #; ipureintro; exact Hnn.2
    (try wp_auto)
    $k))

set_option hygiene false in
/-- `verify.Assert` of the control response's check, its condition computed to `true`. -/
local macro "ctrl_assert" : tactic => `(tactic| (
  wp_apply wp_slice_literal (V := GoInterface) [_, _]
  isplitr
  · ipureintro; rfl
  iintro %asl -
  wp_auto
  wp_apply hAssert))

set_option hygiene false in
/-- **A received mvcc watch response, sent or buffered** (the `sendWatch` closure, called by the
loop's `watchStream.Chan()` case and the drain before a `Created` response, unit W-K; its spec
`HsW`), from the receive (`Hres`) to the closure's result: `true` (`Htrue`, with the responses
sent `Dn`) or, a send failed, `false` (`Hfalse`). -/
local macro "watch_resp" : tactic => `(tactic| (
  icases Hres with ⟨%x, Hwc, #HrI⟩
  -- the received list's authority, and its lower bound, at the receipt
  imod (monoListAuthOwn_update_app (γ := r.γr) [x]) $$ HA with ⟨HA, #Hlbx0⟩
  ihave #Hlbx : v3rpc.rcvLb (GF := GF) r.γr (rcv ++ [x]) $$ []
  · iunfold v3rpc.rcvLb; iexact Hlbx0
  iunfold v3rpc.sendSt at HS
  icases HS with ⟨%S, %pend, %IM, %PM, %M, %HSI, HIM, HPM, Hcaps, #Hpsl, #HM, #Hrok⟩
  obtain ⟨hI, hD, hPM, hL, hH, hMI⟩ := HSI
  -- the snapshot after the receipt (O4), with the announced ids' registry entries
  imod v3rpc.snap_after_recv (v3rpc.cancelQ r.γs) hP hRok r.W r.srv.wsl (interface.mkOk wsty wsv)
    r.ι r.γreg r.γtok r.γcl (rcv ++ [x]) M $$ [Hwc] with ⟨Hwc, %σx, %Sx, Hsnap0, %HMS⟩
  · iframe Hwc Hwstream Hinv HW HM
  ihave Hsnap1 := v3rpc.rcvSnapG_dup (v3rpc.cancelQ r.γs) hP r.W r.srv.wsl r.γreg (rcv ++ [x]) σx Sx
    $$ [Hsnap0]
  · iframe HW Hsnap0
  icases Hsnap1 with #Hsnap
  ihave #Hrok2 := v3rpc.rcvOk_snoc r rcv x σx Sx $$ [Hrok Hlbx]
  · iframe Hrok Hlbx
    iintro !>; iunfold v3rpc.rcvSnap; iexact Hsnap
  ihave #HrI' := HrI
  iunfold mvcc.api.wrespIs at HrI'
  icases HrI' with ⟨%HwvI, %ps, #Hps, %Hpsl, #Hevs⟩
  ihave %Hpsn := ownSlice_len _ _ _ $$ Hps
  wp_auto
  wp_apply time.wp_Now as %tm -
  wp_apply (wp_slice_make2 (V := Loc) wv.Events'.len) as %esl ⟨Hesl, Hecap⟩
  · ipureintro; exact Hpsn.2
  wp_apply sync.RWMutex.wp_RLock (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) $$ [Hmu]
    as ⟨Hrl, HP⟩
  · iframe Hmu
  iunfold v3rpc.swsMu at HP
  icases HP with ⟨%PM2, %VM, %FM, HPm, HVm, HFm, %HVF⟩
  (try wp_auto)
  wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool r.vm VM
    wv.WatchID' _) $$ HVm as HVm
  rw [(HVF wv.WatchID').1]
  simp only [Option.getD_none]
  wp_apply sync.RWMutex.wp_RUnlock (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm)
    $$ [Hrl HPm HVm HFm] as Hmu
  · iframe Hrl; iframe #
    inext
    iunfold v3rpc.swsMu
    iexists PM2, VM, FM
    iframe
    ipureintro; exact HVF
  rename_i iu_ptr
  irename : (iu_ptr ↦ zero_val w64 : IProp GF) => iu
  have Hpsl' : ps.length = sint.nat wv.Events'.len := Hpsn.1
  ihave HC : iprop(∃ (n k : w64), "i" ∷ i_ptr ↦ n ∗ "iu" ∷ iu_ptr ↦ k ∗
      "Hesl" ∷ esl ↦* (ps.take (sint.Z n).toNat ++
        List.replicate (ps.length - (sint.Z n).toNat) (zero_val Loc)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ ps.length⌝) $$ [i iu Hesl]
  · iexists W64 0, _
    iframe i iu
    simp only [show sint.Z (W64 0) = 0 from rfl, Int.toNat_zero, List.take_zero, List.nil_append,
      Nat.sub_zero, Hpsl']
    iframe Hesl
    ipureintro; omega
  wp_for HC
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z wv.Events'.len := by
      first
      | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
      | exact Hif
    have hkP : (sint.Z n).toNat < ps.length := by rw [Hpsl']; word
    obtain ⟨pe, hpe⟩ : ∃ pe, ps[(sint.Z n).toNat]? = some pe := ⟨_, List.getElem?_eq_getElem hkP⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z wv.Events'.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index wv.Events' (sint.Z n) ps DFrac.discard pe Hn.1 $$ [] as -
    · iframe Hps; ipureintro; exact hpe
    (try wp_auto)
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index wv.Events' (sint.Z n) ps DFrac.discard pe Hn.1 $$ [] as -
    · iframe Hps; ipureintro; exact hpe
    (try wp_auto)
    ihave %Hel := ownSlice_len _ _ _ $$ Hesl
    have HlenL : (ps.take (sint.Z n).toNat ++
        List.replicate (ps.length - (sint.Z n).toNat) (zero_val Loc)).length = ps.length := by
      simp; omega
    have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z esl.len := by
      refine ⟨Hn.1, ?_⟩
      have h1 := Hel.1
      rw [HlenL] at h1
      word
    simp only [Hbnd2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index esl (sint.Z n) _ pe $$ [Hesl] as Hesl
    · iframe Hesl; ipureintro; rw [HlenL]; omega
    (try wp_auto)
    rw [show (zero_val Bool) = false from rfl]
    wp_auto
    wp_for_post
    iframe
    have hj1 : sint.Z (n + W64 1) = sint.Z n + 1 := by word
    iexists (n + W64 1), _
    iframe
    have hpe' : ps[(sint.Z n).toNat] = pe := (List.getElem?_eq_some_iff.1 hpe).2
    rw [hj1, show (sint.Z n + 1).toNat = (sint.Z n).toNat + 1 by omega, ← hpe',
      v3rpc.take_replicate_set ps (zero_val Loc) hkP]
    iframe Hesl
    ipureintro; omega
  have hnl : ¬ sint.Z n < sint.Z wv.Events'.len := by
    first
    | exact Hif
    | (intro h; apply Hif; rw [decide_eq_true h])
  have hnE : (sint.Z n).toNat = ps.length := by rw [Hpsl'] at Hn ⊢; word
  rw [hnE, List.take_length, Nat.sub_self, List.replicate_zero, List.append_nil]
  imod ownSlice_persist $$ Hesl with #Hesl
  wp_apply hHdr sws r Up Dn st ci cd wv.Revision' as %hh ⟨%tt, %ll, #Hhdr⟩
  · iframe #
  (try wp_auto)
  irename «$r0» => Hwr
  ihave %Hwrn := typedPointsto_not_null _ _ _ $$ Hwr
  ipersist Hwr
  -- (watches across a compaction, D6) the compaction revision as mvcc's response has it, canceled
  -- if set
  have hCR : wv.CompactRevision' = x.compactRev := HwvI.2.2
  ihave #Hmsg : v3rpc.watchRespMsg «$r0_ptr»
      (v3rpc.mvccResp rcv.length x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩) $$ []
  · iapply (v3rpc.watchRespMsg_intro «$r0_ptr»
      (etcdserverpb.WatchResponse.mk _ hh wv.WatchID' false (!decide (wv.CompactRevision' = W64 0))
        wv.CompactRevision' [] false esl slice.nil 0)
      (v3rpc.mvccResp rcv.length x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩) ps
      (by simp [v3rpc.mvccResp, HwvI.1]) rfl (by simp [v3rpc.mvccResp, hCR])
      (by simp [v3rpc.mvccResp, hCR]) rfl rfl (by simp [v3rpc.mvccResp, Hpsl]))
    simp only [v3rpc.mvccResp]
    iframe Hwr Hhdr Hesl
    isplitr
    · ipureintro; exact Hwrn
    iexact Hevs
  rw [HwvI.1]
  by_cases hd : ((IM !! x.id).isSome = true ∨ x.id = W64 (-1))
  · -- an announced id, or `-1`: the response is sent (after the `if` on the id, once)
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
        ownMap idsL (DFrac.own 1) IM ∗ wresp_ptr ↦ wv))) $$ [HIM wresp]
    rotate_left
    · iintro %v ⟨%Hv, HIM, wresp⟩
      subst Hv
      (try wp_auto)
      wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) _)
      iapply Hrep
      · ipureintro; first | exact Hpsn.2 | omega | word
      iintro !> -
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RLock (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) $$ [Hmu]
        as ⟨Hrl, HP⟩
      · iframe Hmu
      iunfold v3rpc.swsMu at HP
      icases HP with ⟨%PM2, %VM, %FM, HPm, HVm, HFm, %HVF⟩
      (try wp_auto)
      wp_apply (wp_map_lookup2 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool r.fm FM
        wv.WatchID' _) $$ HFm as HFm
      simp only [(HVF wv.WatchID').2, Option.getD_none, Option.isSome_none, decide_false]
      wp_apply sync.RWMutex.wp_RUnlock (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm)
        $$ [Hrl HPm HVm HFm] as Hmu
      · iframe Hrl; iframe #
        inext
        iunfold v3rpc.swsMu
        iexists PM2, VM, FM
        iframe
        ipureintro; exact HVF
      (try wp_auto)
      rw [show (zero_val Bool) = false from rfl]
      (try wp_auto)
      (try rw [Hsi])
      (try wp_auto)
      ihave ⟨Hst, #Hlb⟩ := v3rpc.srvSendTok_lb _ _ $$ Hst
      ihave HDn : Dn D.length (v3rpc.mvccResp rcv.length x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩) $$ []
      · iunfold v3rpc.watchStreamSpec at Hspec
        icases Hspec $$ %D.length %(v3rpc.mvccResp rcv.length x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩)
          with ⟨-, Hb⟩
        iapply Hb
        iunfold v3rpc.watchDn
        iexists r
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        iframe Haux
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        iright
        iunfold v3rpc.mvccOk
        iexists rcv.length, x, rcv, D, σx, Sx
        isplitr
        · ipureintro
          refine ⟨rfl, HwvI.2.1, rfl, rfl, fun hn => (hL _ hn).1 (hd.resolve_right hn), ?_, ?_,
            v3rpc.src_fresh hD rcv.length (fun h => absurd (hI.bound _ h) (Nat.lt_irrefl _)),
            v3rpc.fwdIdx_direct x (v3rpc.sent_idx hD hI.bound),
            fun X => v3rpc.fwdEvs_direct hI hL hD x X⟩
          · intro _ X hl hX
            obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (hMI X hX ((hL X hX).2 hl))
            obtain ⟨w, hw, -⟩ := HMS X i hi
            rw [hw]; rfl
          · intro hev
            have hc := v3rpc.send_claim_direct hI hd hev (fun _ _ _ _ _ _ h _ _ => h)
            rw [v3rpc.filterMap_snoc_bound _ _ _ hI.bound] at hc
            unfold v3rpc.sentEvsOf
            rw [hD, v3rpc.srcOf_snd]
            exact hc
        isplitr
        · ihave #Hlb' := Hlb
          iunfold v3rpc.downLb at Hlb'
          iexact Hlb'
        iframe Hlbx
        iunfold v3rpc.rcvSnap
        iexact Hsnap
      wp_bind (App (Val #(methods si.ty go!"Send" si.v)) (Val #«$r0_ptr»))
      iapply HSend $$ [Hst HDn]
      · iframe Hst HDn Hmsg
      iintro !> %serr Hsr
      icases Hsr with (⟨%Hserr, Hst⟩ | ⟨%Hne, #Hse, Hst⟩)
      rotate_left
      · send_fail (iapply Hfalse; ret_frame)
      subst Hserr
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Lock_guard (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) $$ []
        as ⟨Hlk, HP⟩
      · iframe #
      iunfold v3rpc.swsMu at HP
      icases HP with ⟨%PM3, %VM3, %FM3, HPm, HVm, HFm, %HVF3⟩
      (try wp_auto)
      -- `if len(evs) > 0 && sws.progress[wresp.WatchID]` (then the rest, once)
      wp_bind (If (If _ _ _) _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
          (∃ PMx : GMap w64 Bool, ownMap r.pm (DFrac.own 1) PMx) ∗ wresp_ptr ↦ wv))) $$ [HPm wresp]
      rotate_left
      · iintro %v ⟨%Hv, ⟨%PMx, HPm⟩, wresp⟩
        subst Hv
        (try wp_auto)
        wp_apply sync.RWMutex.wp_Unlock_guard (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm)
          $$ [Hlk HPm HVm HFm]
        · iframe #
          iframe Hlk
          inext
          iunfold v3rpc.swsMu
          iexists _, VM3, FM3
          iframe HPm HVm HFm
          ipureintro; exact HVF3
        wp_apply time.wp_Since as %du -
        wp_apply hSecP _ du $$ [totalDur] as %fs totalDur
        · iframe totalDur; try iframe #
        observe hs1 Ho1
        (try wp_auto)
        wp_apply hSecP _ du $$ [totalDur] as %fs2 totalDur
        · iframe totalDur; try iframe #
        (try wp_auto)
        observe hs2 Ho2
        (try wp_auto)
        obtain ⟨Dn, hDn⟩ : ∃ Dn : List v3rpc.WatchRespM, Dn = D ++ [v3rpc.mvccResp rcv.length x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩] := ⟨_, rfl⟩
        iapply Htrue $$ %x %Dn
        subst hDn
        iframe
        iunfold v3rpc.sendSt
        iexists S ++ [rcv.length], pend, IM, PM, M
        ihave #Hpsl2 := v3rpc.pendSls_snoc r rcv x pend PM $$ Hpsl
        iframe HIM HPM Hcaps Hpsl2 HM Hrok2
        ipureintro
        refine ⟨v3rpc.sendInv_recv_direct hI hd, ?_, hPM,
            v3rpc.idsLive_src _ _ _ (by simp [v3rpc.mvccResp]) hL,
            v3rpc.sendHist_send _ x rcv.length rfl
              (fun X k hX hl hk hkS => absurd
                (v3rpc.live_sent (v3rpc.sendInv_recv_direct hI hd) hL X hX hl hk) hkS)
              (v3rpc.sendHist_recv x (v3rpc.sent_idx hD hI.bound) hH), hMI⟩
        exact v3rpc.srcOf_send (rcv ++ [x]) S rcv.length x (by simp) D _ rfl
          (by rw [v3rpc.srcOf_snoc _ _ _ hI.bound]; exact hD)
      by_cases hl : sint.Z (W64 0) < sint.Z wv.Events'.len
      · simp only [hl, _root_.decide_true, ↓reduceIte]
        (try wp_auto)
        wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool r.pm PM3
          wv.WatchID' _) $$ HPm as HPm
        cases hb : (PM3 !! wv.WatchID').getD false
        · (try wp_auto)
          isplitr
          · ipureintro; rfl
          iframe wresp
          iexists _
          iexact HPm
        · (try wp_auto)
          wp_apply (wp_mapInsert go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty r.pm PM3
            wv.WatchID' false) $$ HPm as HPm
          (try wp_auto)
          isplitr
          · ipureintro; rfl
          iframe wresp
          iexists _
          iexact HPm
      · simp only [hl, decide_false, ↓reduceIte]
        (try wp_auto)
        isplitr
        · ipureintro; rfl
        iframe wresp
        iexists _
        iexact HPm
    by_cases h1 : x.id = W64 (-1)
    all_goals (
      simp only [h1, _root_.decide_true, decide_false, Bool.not_true, Bool.not_false, ↓reduceIte]
      (try wp_auto)
      first
      | (have hIMs : (IM !! wv.WatchID').isSome = true := (by rw [HwvI.1]; exact hd.resolve_right h1); wp_apply (wp_map_lookup2 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty (go.StructType []) idsL IM wv.WatchID' (DFrac.own 1)) $$ HIM as HIM; simp only [hIMs, _root_.decide_true, Bool.not_true, ↓reduceIte]; (try wp_auto))
      | skip
      isplitr
      · ipureintro; rfl
      iframe HIM wresp)
  · have hX1 : x.id ≠ W64 (-1) := fun h => hd (Or.inr h)
    have hIMn : (IM !! x.id) = none := by
      cases h : IM !! x.id with
      | none => rfl
      | some _ => exact absurd (Or.inl (by simp [h])) hd
    simp only [hX1, decide_false, Bool.not_false, ↓reduceIte]
    have hIMn' : IM !! wv.WatchID' = none := by rw [HwvI.1]; exact hIMn
    (try wp_auto)
    wp_apply (wp_map_lookup2 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty (go.StructType [])
      idsL IM wv.WatchID' (DFrac.own 1)) $$ HIM as HIM
    simp only [hIMn', Option.isSome_none, decide_false]
    (try wp_auto)
    wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
      (go.GoType.SliceType (go.GoType.PointerType etcdserverpb.WatchResponse.ty)) pendL PM wv.WatchID'
      (DFrac.own 1)) $$ HPM as HPM
    rw [HwvI.1]
    ihave ⟨Hcap0, Hcaps⟩ := v3rpc.pendCaps_take PM x.id $$ Hcaps
    ihave #Hsl0 : v3rpc.pendSl r rcv (pend x.id) ((PM !! x.id).getD (zero_val GoSlice)) $$ []
    · cases hX : PM !! x.id with
      | some sl =>
        simp only [Option.getD_some]
        iapply BigSepM.bigSepM_lookup (Φ := fun Y sl => v3rpc.pendSl (GF := GF) r rcv (pend Y) sl) hX
          $$ Hpsl
      | none =>
        rw [hPM _ hX]
        simp only [Option.getD_none]
        iunfold v3rpc.pendSl
        iexists [], []
        isplitr
        · iapply ownSlice_nil
        isplitr
        · ipureintro; simp
        simp
        iempintro
    iunfold v3rpc.pendSl at Hsl0
    icases Hsl0 with ⟨%ls, %xs, #Hls, %Hxs, #Hmsgs⟩
    (try wp_auto)
    wp_apply wp_slice_literal (V := Loc) [«$r0_ptr»]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply (wp_slice_append_persistent _ ls _ [«$r0_ptr»] (DFrac.own 1)) $$ [Hcap0 Hsl2]
      as %sl' ⟨#Hsl', Hcap', -⟩
    · iframe Hls Hcap0 Hsl2
    wp_apply (wp_mapInsert go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty pendL PM wv.WatchID' sl')
      $$ HPM as HPM
    rw [HwvI.1]
    (try wp_auto)
    obtain ⟨Dn, hDn⟩ : ∃ Dn : List v3rpc.WatchRespM, Dn = D := ⟨_, rfl⟩
    iapply Htrue $$ %x %Dn
    subst hDn
    iframe
    iunfold v3rpc.sendSt
    iexists S, v3rpc.upd pend x.id (pend x.id ++ [rcv.length]), IM, (<[x.id := sl']> PM), M
    ihave #Hpsl2 := v3rpc.pendSls_snoc r rcv x pend PM $$ Hpsl
    ihave #Hnew : v3rpc.pendSl r (rcv ++ [x]) (pend x.id ++ [rcv.length]) sl' $$ []
    · iunfold v3rpc.pendSl
      iexists ls ++ [«$r0_ptr»], xs ++ [(x, ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩)]
      iframe Hsl'
      isplitr
      · ipureintro
        refine ⟨by simp [Hxs.1], ?_, ?_⟩
        · rw [List.map_append, v3rpc.map_snoc_some rcv x _ xs Prod.fst Hxs.2.1]
          simp
        · intro p hp
          rw [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact Hxs.2.2 p hp
          · exact ⟨rfl, rfl, HwvI.2.1⟩
      rw [List.zip_append Hxs.1]
      iapply BigSepL.bigSepL_append.2
      iframe Hmsgs
      simp only [List.zip_cons_cons, List.zip_nil_left]
      iapply BigSepL.bigSepL_singleton.2
      iapply v3rpc.watchRespMsg_mvccResp $$ Hmsg
    ihave ⟨Hcaps, Hpsl3⟩ := v3rpc.pendMaps_insert r (rcv ++ [x]) pend PM x.id sl'
      (pend x.id ++ [rcv.length]) $$ [Hcaps Hcap']
    · iframe Hcaps Hcap' Hpsl2 Hnew
    iframe HIM HPM Hcaps Hpsl3 HM Hrok2
    ipureintro
    refine ⟨v3rpc.sendInv_recv_pend hI (by simpa using hd), ?_, ?_, hL,
      v3rpc.sendHist_recv x (v3rpc.sent_idx hD hI.bound) hH, hMI⟩
    · rw [v3rpc.srcOf_snoc _ _ _ hI.bound]; exact hD
    · intro Y hY
      by_cases h : Y = x.id
      · subst h; rw [GMap.lookup_insert] at hY; cases hY
      · rw [v3rpc.upd_ne _ _ h]
        apply hPM
        rw [GMap.lookup_insert_ne _ _ (Ne.symm h)] at hY
        exact hY))

set_option hygiene false in
/-- **A created response for `X` sent**: `X` announced (`ids[X]`), its buffered responses
flushed in order (`send_claim_flush`), `pending[X]` deleted. -/
local macro "ctrl_created" X:term : tactic => `(tactic| (
  iunfold v3rpc.sendSt at HS
  icases HS with ⟨%S, %pend, %IM, %PM, %M, %HSI, HIM, HPM, Hcaps, #Hpsl, #HM, #Hrok⟩
  obtain ⟨hI, hD, hPM, hL, hH, hMI⟩ := HSI
  icases v3rpc.regMap_created r D.length m $X IM M hX hcr (fun hca => Hcc hca hcr) hMI $$ [HM Hord]
    with ⟨%M', #HM', %hMI'⟩
  · iframe HM Hord
  wp_apply (wp_mapInsert go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty idsL IM $X ()) $$ HIM
    as HIM
  have hids : (fun Y => ((<[$X := ()]> IM) !! Y).isSome) =
      v3rpc.upd (fun Y => (IM !! Y).isSome) $X true := by
    funext Y; unfold v3rpc.upd; by_cases h : Y = $X
    · subst h; simp [GMap.lookup_insert]
    · simp [h, Ne.symm h]
  have hI1 := v3rpc.sendInv_created $X hI
  rw [← hids] at hI1
  have hL1 := v3rpc.idsLive_created D m IM $X Hm.2.2 hX hL hok
  (try wp_auto)
  wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
    (go.GoType.SliceType (go.GoType.PointerType etcdserverpb.WatchResponse.ty)) pendL PM $X
    (DFrac.own 1)) $$ HPM as HPM
  ihave #Hsl0 : v3rpc.pendSl r rcv (pend $X) ((PM !! $X).getD (zero_val GoSlice)) $$ []
  · cases hX : PM !! $X with
    | some sl =>
      simp only [Option.getD_some]
      iapply BigSepM.bigSepM_lookup (Φ := fun Y sl => v3rpc.pendSl (GF := GF) r rcv (pend Y) sl) hX
        $$ Hpsl
    | none =>
      rw [hPM _ hX]
      simp only [Option.getD_none]
      iunfold v3rpc.pendSl
      iexists [], []
      isplitr
      · iapply ownSlice_nil
      isplitr
      · ipureintro; simp
      simp
      iempintro
  iunfold v3rpc.pendSl at Hsl0
  icases Hsl0 with ⟨%ls, %xs, #Hls, %Hxs, #Hmsgs⟩
  ihave %Hlsl := ownSlice_len _ _ _ $$ Hls
  have HlenP : (pend $X).length = xs.length := by
    have := congrArg List.length Hxs.2.1; simpa using this
  ihave #Hrok' := Hrok
  iunfold v3rpc.rcvOk at Hrok'
  ihave HF : iprop(∃ (j : w64) (vv : Loc) (D' : List v3rpc.WatchRespM),
      "i" ∷ i_ptr ↦ j ∗ "v" ∷ v_ptr ↦ vv ∗
      "Hst" ∷ v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs D' ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ (sint.Z j).toNat ≤ (pend $X).length ∧
        v3rpc.SendInv rcv (S ++ (pend $X).take (sint.Z j).toNat)
          (v3rpc.upd pend $X ((pend $X).drop (sint.Z j).toNat))
          (fun Y => ((<[$X := ()]> IM) !! Y).isSome) (some $X) ∧
        D'.filterMap v3rpc.WatchRespM.src = v3rpc.srcOf rcv (S ++ (pend $X).take (sint.Z j).toNat) ∧
        (∀ Y, Y ≠ W64 (-1) → (((<[$X := ()]> IM) !! Y).isSome = true ↔ v3rpc.idLive D' Y)) ∧
        v3rpc.SendHist rcv D' (S ++ (pend $X).take (sint.Z j).toNat)⌝)
        $$ [i v Hst]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by decide, by simp, ?_, ?_, hL1, ?_⟩
    · simp only [show sint.Z (W64 0) = 0 from rfl, Int.toNat_zero, List.take_zero, List.append_nil,
        List.drop_zero, v3rpc.upd_self]
      exact hI1
    · simp only [show sint.Z (W64 0) = 0 from rfl, Int.toNat_zero, List.take_zero, List.append_nil]
      exact v3rpc.srcOf_ctrl rcv S D m Hm.2.2 hD
    · simp only [show sint.Z (W64 0) = 0 from rfl, Int.toNat_zero, List.take_zero, List.append_nil]
      exact v3rpc.sendHist_ctrl m Hm.2.2 hH
  wp_for HF
  obtain ⟨Hj0, HjP, hIk, hDk, hLk, hHk⟩ := Hj
  wp_if_destruct
  · have Hif' : sint.Z j < sint.Z ((PM !! $X).getD (zero_val GoSlice)).len := by
      first
      | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
      | exact Hif
    have Hlen1 := Hlsl.1
    have hkP : (sint.Z j).toNat < (pend $X).length := by rw [HlenP, ← Hxs.1]; word
    obtain ⟨l, hl⟩ : ∃ l, ls[(sint.Z j).toNat]? = some l :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    obtain ⟨xp, hxp⟩ : ∃ xp, xs[(sint.Z j).toNat]? = some xp :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hxs.1]; word)⟩
    obtain ⟨n, hn⟩ : ∃ n, (pend $X)[(sint.Z j).toNat]? = some n :=
      ⟨_, List.getElem?_eq_getElem hkP⟩
    have hrn : rcv[n]? = some xp.1 := v3rpc.map_some_get rcv (pend $X) xs Prod.fst Hxs.2.1 hn hxp
    have hxpF := Hxs.2.2 xp (List.mem_of_getElem? hxp)
    have hz : (ls.zip xs)[(sint.Z j).toNat]? = some (l, xp) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hl, hxp⟩
    ihave #Hml := BigSepL.bigSepL_lookup
      (Φ := fun _ q => v3rpc.watchRespMsg (GF := GF) q.1 (v3rpc.mvccResp 0 q.2.1 q.2.2)) hz $$ Hmsgs
    ihave #Hml2 := v3rpc.watchRespMsg_mvccResp l 0 n xp.1 xp.2 $$ Hml
    ihave #Hml' := Hml
    iunfold v3rpc.watchRespMsg at Hml'
    icases Hml' with ⟨%Hln', %h', %esl', %eps', -, -, -, -, -, -, -, -, #HEv', #HEsl, -⟩
    ihave %HEsl' := ownSlice_len _ _ _ $$ HEsl
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ((PM !! $X).getD (zero_val GoSlice)).len := ⟨Hj0, Hif'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z j) ls DFrac.discard l Hj0 $$ [] as -
    · iframe Hls; ipureintro; exact hl
    (try wp_auto)
    wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) _)
    iapply Hrep
    · ipureintro; first | exact HEsl'.2 | omega | word
    iintro !> -
    (try wp_auto)
    have hpk : (v3rpc.upd pend $X ((pend $X).drop (sint.Z j).toNat)) $X =
        n :: (pend $X).drop ((sint.Z j).toNat + 1) := by
      obtain ⟨_, hnk⟩ := List.getElem?_eq_some_iff.1 hn
      rw [v3rpc.upd_same, List.drop_eq_getElem_cons hkP, hnk]
    ihave ⟨Hst, #Hlb⟩ := v3rpc.srvSendTok_lb _ _ $$ Hst
    have hX0 : $X ≠ W64 (-1) := fun h => by
      have := hI.noPend $X (Or.inr h) (by simp)
      rw [this] at hn; simp at hn
    have hxid : xp.1.id = $X := v3rpc.pend_id hIk hpk hrn
    have htk : rcv.take (n + 1) = rcv.take n ++ [xp.1] := by
      rw [List.take_add_one, hrn]; simp
    have hln : (rcv.take n).length = n := by
      rw [List.length_take]; have := (List.getElem?_eq_some_iff.1 hrn).1; omega
    ihave ⟨#HlbN, %σn, %Sn, #HsnN⟩ := Hrok' $$ %n %xp.1 %hrn
    ihave HDn : Dn D'.length (v3rpc.mvccResp n xp.1 xp.2) $$ []
    · iunfold v3rpc.watchStreamSpec at Hspec
      icases Hspec $$ %D'.length %(v3rpc.mvccResp n xp.1 xp.2) with ⟨-, Hb⟩
      iapply Hb
      iunfold v3rpc.watchDn
      iexists r
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe Haux
      isplitr
      · ipureintro; exact ⟨hxpF.1, hxpF.2.1⟩
      iright
      iunfold v3rpc.mvccOk
      iexists n, xp.1, rcv.take n, D', σn, Sn
      isplitr
      · ipureintro
        refine ⟨rfl, hxpF.2.2, rfl, hln,
          fun hn' => (hLk _ hn').1 (by rw [hxid]; simp [GMap.lookup_insert]),
          fun h => absurd (hxid.symm.trans h) hX0, ?_,
          v3rpc.src_fresh hDk n (v3rpc.pend_not_sent hIk hpk),
          v3rpc.fwdIdx_flush hIk hpk hHk xp.1 hxid hX0,
          fun Y => v3rpc.fwdEvs_flush hIk hpk hDk xp.1 hxid hX0 Y⟩
        intro hev
        obtain ⟨-, hc⟩ := v3rpc.send_claim_flush hIk hpk hrn hev (fun _ _ _ _ _ _ h _ _ => h)
        rw [htk] at hc
        unfold v3rpc.sentEvsOf
        rw [hDk, v3rpc.srcOf_snd]
        exact hc
      isplitr
      · ihave #Hlb' := Hlb
        iunfold v3rpc.downLb at Hlb'
        iexact Hlb'
      rw [← htk]
      iframe HlbN
      iunfold v3rpc.rcvSnap
      iexact HsnN
    wp_bind (App (Val #(methods si.ty go!"Send" si.v)) (Val #l))
    iapply HSend $$ [Hst HDn]
    · iframe Hst HDn Hml2
    iintro !> %serr Hsr
    icases Hsr with (⟨%Hserr, Hst⟩ | ⟨%Hne, #Hse, Hst⟩)
    rotate_left
    · send_fail ret_exit
    subst Hserr
    (try wp_auto)
    wp_for_post
    iframe
    have hj1 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
    iexists (j + W64 1), _, _
    iframe
    ipureintro
    have hk1 : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by rw [hj1]; omega
    rw [hk1, List.take_add_one, hn]
    simp only [Option.toList_some]
    refine ⟨by omega, by omega, ?_, ?_, v3rpc.idsLive_src _ _ _ (by simp [v3rpc.mvccResp]) hLk, ?_⟩
    · have := v3rpc.sendInv_flush hIk hpk
      rw [v3rpc.upd_upd] at this
      rw [← List.append_assoc]
      exact this
    · rw [← List.append_assoc]
      exact v3rpc.srcOf_send rcv _ n xp.1 hrn D' _ rfl hDk
    · rw [← List.append_assoc]
      exact v3rpc.sendHist_send _ xp.1 n rfl (v3rpc.hnew_flush hIk hpk hLk) hHk
  · have hnl : ¬ sint.Z j < sint.Z ((PM !! $X).getD (zero_val GoSlice)).len := by
      first
      | exact Hif
      | (intro h; apply Hif; rw [decide_eq_true h])
    (try simp only [hnl, decide_false, eq_self_iff_true, _root_.decide_true, ↓reduceIte])
    have Hlen1 := Hlsl.1
    have hkE : (sint.Z j).toNat = (pend $X).length := by rw [HlenP, ← Hxs.1] at HjP ⊢; word
    rw [hkE, List.take_length, List.drop_length] at hIk
    rw [hkE, List.take_length] at hDk hHk
    (try wp_auto)
    wp_apply (wp_mapDelete pendL PM $X go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
      (go.GoType.SliceType (go.GoType.PointerType etcdserverpb.WatchResponse.ty))) $$ HPM as HPM
    wp_apply time.wp_Since as %du -
    wp_apply hSec du as %fs -
    observe hs3 Ho3
    (try wp_auto)
    wp_for_post
    iframe
    iexists rcv, cs ++ [cl], D'
    iframe
    iunfold v3rpc.sendSt
    iexists (S ++ pend $X), (v3rpc.upd pend $X []), (<[$X := ()]> IM), (GMap.delete $X PM), M'
    ihave ⟨Hcaps, Hpsl'⟩ := v3rpc.pendMaps_delete r rcv pend PM $X $$ [Hcaps Hpsl]
    · iframe Hcaps Hpsl
    iframe HIM HPM Hcaps Hpsl' HM' Hrok
    ipureintro
    refine ⟨?_, hDk, ?_, hLk, hHk, hMI'⟩
    · have := v3rpc.sendInv_flush_done' hIk (by simp)
      rw [v3rpc.upd_upd] at this
      exact this
    · intro Y hY
      by_cases h : Y = $X
      · subst h; simp
      · rw [v3rpc.upd_ne _ _ h]
        apply hPM
        rw [GMap.lookup_delete_ne _ (Ne.symm h)] at hY
        exact hY))

set_option hygiene false in
/-- The drain's invariant after a response it sent or buffered (`sendWatch` returned `true`; not
drained, `hdr0`). -/
local macro "drain_exit" : tactic => `(tactic| (
  iexists rcv ++ [x], Dn, dr
  isplitr
  · ipureintro; intro hd; rw [hdr0] at hd; cases hd
  isplitr
  · rw [hdr0]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial))

set_option hygiene false in
/-- **The drain before a created response** (unit W-K): the watch responses queued on the
channel are sent (`sendWatch`, `HsW`) until a non-blocking receive finds it empty
(`drain_poll`, at the watcher's stamp `k0`, `Hk0`), which shows that the stamp is at most the
responses received; after the loop, `Hdl`, and the received list's lower bound `Hrs`. -/
local macro "drain_created" : tactic => `(tactic| (
  ihave HId : iprop(∃ (rcv : List mvcc.api.WResp) (D : List v3rpc.WatchRespM) (dr : Bool),
      "%Hdl" ∷ ⌜dr = true → k0 ≤ rcv.length⌝ ∗
      "#Hrs" ∷ (if dr then v3rpc.rcvLb r.γr rcv else iprop(True)) ∗
      "Hst" ∷ v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs D ∗
      "Hwc" ∷ mvcc.api.wsRecv r.ι rcv ∗ "HA" ∷ monoListAuthOwn r.γr 1 rcv ∗ "Htt" ∷ v3rpc.sendTok r ∗
      "HS" ∷ v3rpc.sendSt r idsL pendL rcv D ∗
      "drained" ∷ drained_ptr ↦ dr) $$ [Hst Hwc HA Htt HS drained]
  · iexists rcv, D, false
    isplitr
    · ipureintro; intro h; cases h
    isplitr
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    iframe
  wp_for HId
  wp_if_destruct
  · have hdr0 : dr = false := by
      cases dr
      · rfl
      · exact absurd (GoGlobalContext.intoVal_inj_bool Hif) (by decide)
    wp_apply +noauto (hCh r.W.γm r.ι) $$ [] as %ch' %Hch'
    · iframe #
    subst Hch'
    wp_auto
    wp_bind (App (Val (GoInstruction SelectStmt)) _)
    iapply (chan.wp_select_nonblocking_alt [iprop(⌜k0 ≤ rcv.length⌝ ∗ v3rpc.rcvLb r.γr rcv)] _ _ _ _)
      $$ [] [-] []
    all_goals first | iNamedAccu | skip
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro __CTX
      iNamed __CTX
      simp only [chan.nonblockingAltClausePre]
      iexists go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse, inferInstance, inferInstance,
        inferInstance, inferInstance, mvcc.api.wsChanOf r.ι, mvcc.api.wsChanNames r.ι
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hch
      iapply Hpoll $$ %rcv %k0 %r.γr Hwc Hk0 HA
      isplit
      · iintro %wv %okw Hres HA
        cases okw
        · simp only [Bool.false_eq_true, ↓reduceIte]
          irename Hres => Hwc
          wp_auto
          ret_mid
        -- `sendWatch(wresp)` (`HsW`)
        try simp only [↓reduceIte]
        wp_auto
        wp_bind (App (App (Val (GoInstruction (GoLoad _))) (Val #sendWatch_ptr)) _)
        iapply HsW $$ Hres HA Htt Hst HS Hmu [-] []
        · iintro %x %Dn ⟨Hst, Hwc, HA, Htt, HS, Hmu⟩
          wp_auto
          wp_for_post
          iframe
          drain_exit
          iframe
        · iintro Hret
          wp_auto
          ret_mid
      · iintro Hwc HA #Hsnap %Hle
        iframe
        iframe #
        ipureintro; exact Hle
    · iintro __CTX Hnr
      iNamed __CTX
      icases (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hnr with ⟨%Hle, #Hsnap⟩
      wp_auto
      wp_for_post
      iframe
      iexists rcv, D, true
      isplitr
      · ipureintro; intro _; exact Hle
      isplitr
      · simp only [↓reduceIte]; iexact Hsnap
      iframe
  wp_if_destruct
  rotate_left
  · exfalso; cases dr <;> simp_all
  have hdr1 : dr = true := by cases dr <;> simp_all
  have Hkrcv : k0 ≤ rcv.length := Hdl hdr1
  irevert Hrs; rw [hdr1]; simp only [↓reduceIte]; iintro #Hrs))

set_option hygiene false in
/-- **The rest of the control case** (from `start := time.Now()`), after the drain of a `Created`
response or without it (unit W-K). -/
local macro "ctrl_rest" : tactic => `(tactic| (
  wp_apply time.wp_Now as %tm -
  rw [Hsi]
  wp_auto
  ihave HDn : Dn D.length m $$ [Hcw Hat]
  · iunfold v3rpc.watchStreamSpec at Hspec
    icases Hspec $$ %D.length %m with ⟨-, Hb⟩
    iapply Hb
    iunfold v3rpc.watchDn
    iexists r
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    iframe Haux
    isplitr
    · ipureintro; exact ⟨Hm.1, Hm.2.1⟩
    ileft
    isplitr
    · ipureintro; exact Hm.2.2
    isplitl [Hcw Hat]
    · iunfold v3rpc.ctrlOk
      iexists ireq, req
      iframe Hupat Hcw Hat
      ipureintro; exact Hans
    iexact Hord
  wp_bind (App (Val #(methods si.ty go!"Send" si.v)) (Val #cl))
  iapply HSend $$ [Hst HDn]
  · iframe Hst HDn Hmsg
  iintro !> %serr Hsr
  icases Hsr with (⟨%Hserr, Hst⟩ | ⟨%Hne, #Hse, Hst⟩)
  · subst Hserr
    ihave #Hmsg' := Hmsg
    iunfold v3rpc.watchRespMsg at Hmsg'
    icases Hmsg' with ⟨%Hln, %hh, %esl, %eps, #HfH, #Hhdr, #HfId, #HfCr, #HfCa, #HfCR, #HfRe, #HfFr,
      #HfEv, #Heps, %Hepsl, #Hevs⟩
    have Hcc : m.canceled = true → m.created = true → m.watchId = W64 (-1) := by
      intro h1 h2
      unfold v3rpc.ctrlAnswers at Hans
      rcases req with c | id | _ | _
      · rcases Hans.2.2.2.2 with ⟨-, (⟨-, h⟩ | ⟨h, -⟩)⟩
        · exact h
        · rw [h1] at h; cases h
      · rw [h2] at Hans; exact absurd Hans.2.2.2.2.1 (by decide)
      · exact Hans.2.2.2.2.elim
      · exact Hans.2.2.2.2.elim
    wp_auto
    cases hcr : m.created
    · cases hca : m.canceled
      · exfalso
        unfold v3rpc.ctrlAnswers at Hans
        rcases req with c | id | _ | _
        · rw [hcr] at Hans; exact absurd Hans.2.2.2.2.1 (by decide)
        · rw [hca] at Hans; exact absurd Hans.2.2.2.2.2.1 (by decide)
        · exact Hans.2.2.2.2.elim
        · exact Hans.2.2.2.2.elim
      · -- canceled, not created: `delete(ids, wid)` unless `wid == -1`, then `continue`
        wp_auto
        ctrl_assert
        iunfold v3rpc.sendSt at HS
        icases HS with ⟨%S, %pend, %IM, %PM, %M, %HSI, HIM, HPM, Hcaps, #Hpsl, #HM, #Hrok⟩
        obtain ⟨hI, hD, hPM, hL, hH, hMI⟩ := HSI
        have hD' : (D ++ [m]).filterMap v3rpc.WatchRespM.src = v3rpc.srcOf rcv S :=
          v3rpc.srcOf_ctrl rcv S D m Hm.2.2 hD
        by_cases hw : m.watchId = W64 (-1)
        · simp only [hw, _root_.decide_true, Bool.not_true, ↓reduceIte]
          wp_auto
          wp_apply time.wp_Since as %du -
          wp_apply hSec du as %fs -
          observe hs3 Ho3
          wp_auto
          wp_for_post
          iframe
          iexists rcv, cs ++ [cl], D ++ [m]
          iframe
          iunfold v3rpc.sendSt
          iexists S, pend, IM, PM, M
          iframe HIM HPM Hcaps Hpsl HM Hrok
          ipureintro
          exact ⟨hI, hD', hPM, v3rpc.idsLive_neg1 _ _ _ Hm.2.2 hw hL, v3rpc.sendHist_ctrl m Hm.2.2 hH,
            hMI⟩
        · simp only [hw, decide_false, Bool.not_false, ↓reduceIte]
          wp_auto
          wp_apply (wp_mapDelete idsL IM m.watchId go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
            (go.StructType [])) $$ HIM as HIM
          (try wp_auto)
          wp_for_post
          iframe
          iexists rcv, cs ++ [cl], D ++ [m]
          iframe
          iunfold v3rpc.sendSt
          iexists S, pend, (GMap.delete m.watchId IM), PM, M
          iframe HIM HPM Hcaps Hpsl HM Hrok
          ipureintro
          refine ⟨?_, hD', hPM, v3rpc.idsLive_canceled _ _ _ _ Hm.2.2 rfl hca hL,
            v3rpc.sendHist_ctrl m Hm.2.2 hH, ?_⟩
          rotate_left
          · intro Y hY hI'
            by_cases h : Y = m.watchId
            · subst h; simp [GMap.lookup_delete] at hI'
            · rw [GMap.lookup_delete_ne _ (Ne.symm h)] at hI'
              exact hMI Y hY hI'
          have hids : (fun Y => ((GMap.delete m.watchId IM) !! Y).isSome) =
              v3rpc.upd (fun Y => (IM !! Y).isSome) m.watchId false := by
            funext Y; unfold v3rpc.upd; by_cases h : Y = m.watchId
            · subst h; simp [GMap.lookup_delete]
            · simp [h, Ne.symm h]
          rw [hids]
          exact v3rpc.sendInv_cancel m.watchId hI
    · -- created (and so `wid == -1` if canceled, `Hcc`): whether canceled or not, the assertion's
      -- condition is `true` and `c.Canceled && wid != -1` false, both joined (`wp_join`), so that
      -- the flush (`ctrl_created`) is verified once
      wp_join (v := #true) at (if: _ then _ else _) with [c wid]
      · cases hca : m.canceled
        · wp_auto
          wp_join_done
        · rw [Hcc hca hcr]
          wp_auto
          wp_join_done
      ctrl_assert
      wp_join at (if: _ then _ else _) with [c wid]
      · cases hca : m.canceled
        · wp_auto
          wp_join_done
        · rw [Hcc hca hcr]
          wp_auto
          wp_join_done
      have hX : m.watchId = m.watchId := rfl
      have hok : m.watchId ≠ W64 (-1) → (m.created && !m.canceled) = true := fun h => by
        cases hca : m.canceled
        · simp [hcr]
        · exact absurd (Hcc hca hcr) h
      (try wp_auto)
      ctrl_created m.watchId
  send_fail ret_exit))

set_option hygiene false in
/-- **The end of the control case's `if c.Created`**: `ctrlMid` (the rest of the control case
follows it, `ctrl_rest`). -/
local macro "ctrl_mid_exec" : tactic => `(tactic| (
  (try wp_auto)
  iapply (v3rpc.ctrlMid_exec r ci sws idsL pendL req m rcv D)
  iframe
  iexact Hord))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

-- (the unused-variables linter walks the whole info tree of this long proof)
set_option linter.unusedVariables false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem v3rpc.serverWatchStream.sendLoop.wp_proof
    (hHdr : v3rpc.serverWatchStream.newResponseHeader.spec (GF := GF) (hG := hG))
    (hGPI : v3rpc.GetProgressReportInterval.spec (GF := GF) (hG := hG))
    (hICE : v3rpc.isClientCtxErr.spec (GF := GF) (hG := hG))
    (hShapes : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hR : mvcc.api.wsChan_recv.law (GF := GF) (hG := hG))
    (hRok : mvcc.api.wsRecv_ok.law (GF := GF) (hG := hG))
    (hZero : mvcc.api.wsSentLb_zero.law (GF := GF) (hG := hG))
    (hAssert : verify.Assert.spec (GF := GF) (hG := hG))
    (hNT : time.NewTicker.spec (GF := GF) (hG := hG))
    (hStop : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hSecP : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (hZD : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hCV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hRER : mvcc.ReportEventReceived.spec (GF := GF) (hG := hG)) :
    v3rpc.serverWatchStream.sendLoop.spec (GF := GF) (hG := hG) := by
  intro sws r Up Dn st ci cd
  have := v3rpc.swsIs_persistent (GF := GF) hP
  wp_start as ⟨#Hsws, Hst, Hcons, Hwc, HA, %Hiv, Hmu, Htt, Hrdr⟩
  have : ∀ ws γ ι, Persistent (mvcc.api.isMvccWatchStream (GF := GF) ws γ ι) := hP.2.1
  have : ∀ ι n, Persistent (mvcc.api.wsSentLb (GF := GF) ι n) := hP.2.2.1
  have := v3rpc.srvWOk_persistent hP r.W r.srv.wsl v3rpc.wsN
  ihave #Hsws' := Hsws
  iunfold v3rpc.swsIs at Hsws'
  icases Hsws' with ⟨%Hnn, #Flg, #Fcid, #Fmid, #Fmrb, #Fsg, #Fwa, #Fag, #Fst, #Fws, #Fctrl, #Fpm,
    #Fvm, #Ffm, #Fcc, #Hsrv, #Hstream, #Hspec, #Haux, #Hup, #Hwstream, #Hinv, #HW, #Hspsc, #Hcc,
    #Hmug⟩
  iunfold v3rpc.wsInv at Hinv
  ihave %Hsh := hShapes.2.2.2 r.ws r.W.γm r.ι $$ Hwstream
  obtain ⟨wsty, wsv, hws, -, hCh, hRP, -, -, -, -⟩ := Hsh
  rw [hws]
  -- the stream's channel: its blocking receive and the drain's poll (`wsChan_recv.law`)
  icases hR (interface.mkOk wsty wsv) r.W.γm r.ι $$ Hwstream with ⟨#Hch, #Hrecvb, -⟩
  icases v3rpc.drain_poll hR (interface.mkOk wsty wsv) r.W.γm r.ι $$ Hwstream with ⟨-, #Hpoll⟩
  ihave #Hsrv' := Hsrv
  iunfold v3rpc.watchSrvOk at Hsrv'
  icases Hsrv' with ⟨#Hrso, #Hauth, #Hvars, -⟩
  ihave #Hvars' := Hvars
  iunfold v3rpc.watchVars at Hvars'
  icases Hvars' with ⟨#Heof, #Hwpv⟩
  iunfold v3rpc.watchPkgVars at Hwpv
  icases Hwpv with ⟨#HeInv, #HeOld, #HeEmpty, #HeDenied, #HeEWR, #HeDup, #HmCompacted,
    #HmInv, #HmOld, #HmEmpty, #HmDenied, #HmWC, #HstreamF, #Hh1, #Hh2, #Hh3, #Hh4, #Htracer,
    #Hcanc, #Hguard⟩
  -- (D19j) `mvcc.ReportEventReceived`'s trust-boundary spec, of a non-negative count
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hrep : iprop(□ ∀ n : w64, {{ ⌜0 ≤ sint.Z n⌝ }}
      (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) (Val #n))
      {{ RET #(); True }}) $$ []
  · iintro !> %n
    iintro !> %Φ' %Hn HΦ'
    wp_apply (hRER n Hn)
    iapply HΦ'
    itrivial
  iunfold v3rpc.histVar at Hh1 Hh2 Hh3 Hh4
  icases Hh1 with ⟨%hs1, #Hg1, #Ho1⟩
  icases Hh2 with ⟨%hs2, #Hg2, #Ho2⟩
  icases Hh3 with ⟨%hs3, #Hg3, #Ho3⟩
  icases Hh4 with ⟨%hs4, #Hg4, #Ho4⟩
  ihave #Hstream' := Hstream
  iunfold v3rpc.srvStreamIs at Hstream'
  icases Hstream' with ⟨%si, %Hsi, #HRecv, #HSend, #HCtx, #Hctxis, #Hrunctx⟩
  ihave #Hctx2 := Hctxis
  iNamed Hctx2
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  icases HstreamF with ⟨%cvF, #HcvF, %HcvFl⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pprom : isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify $$ []
  · iPkgInit
  ihave #Pmvcc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  (try wp_auto)
  wp_bind (App (Val wrapDefer) _)
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Unit) go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
    (go.StructType [])) as %idsL Hids
  wp_apply (wp_map_make1 (K := w64) (V := GoSlice) go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
    (go.GoType.SliceType (go.GoType.PointerType etcdserverpb.WatchResponse.ty))) as %pendL Hpend
  wp_apply hGPI $$ [$Htt] as %d ⟨%Hd, Htt⟩
  · iframe #; ipureintro; exact Hiv
  ihave Htt : v3rpc.sendTok r $$ [Htt Hrdr]
  · unfold v3rpc.sendTok; iframe
  wp_apply hNT d $$ [] as %tk %tch %γt #Htk0
  · ipureintro; exact Hd
  ihave #Htk : iprop(∃ (ch : Loc) (γ : ChanNames), time.isTicker (GF := GF) tk ch γ) $$ []
  · iexists tch, γt; iexact Htk0
  ihave #Htk' := Htk0
  iunfold time.isTicker at Htk'
  icases Htk' with ⟨#HC, #HI, #HR, #Hbag⟩
  ipersist sws
  ipersist ids
  ipersist pending
  ipersist progressTicker
  -- **the `sendWatch` closure** (its spec, for its calls in the loop and in the drain)
  ipersist sendWatch
  ihave #HsW : iprop(□ ∀ (rcv : List mvcc.api.WResp) (D : List v3rpc.WatchRespM)
      (wv : go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse) (Ψ : val → IProp GF),
      (∃ x : mvcc.api.WResp, mvcc.api.wsRecv r.ι (rcv ++ [x]) ∗ mvcc.api.wrespIs wv x) -∗
      monoListAuthOwn r.γr 1 rcv -∗ v3rpc.sendTok r -∗
      v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs D -∗ v3rpc.sendSt r idsL pendL rcv D -∗
      sync.ownRWMutex (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) -∗
      (∀ (x : mvcc.api.WResp) (Dn : List v3rpc.WatchRespM),
        v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs Dn ∗
          mvcc.api.wsRecv r.ι (rcv ++ [x]) ∗ monoListAuthOwn r.γr 1 (rcv ++ [x]) ∗ v3rpc.sendTok r ∗
          v3rpc.sendSt r idsL pendL (rcv ++ [x]) Dn ∗
          sync.ownRWMutex (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) -∗ Ψ #true) -∗
      (v3rpc.retSt r pendL -∗ Ψ #false) -∗
      WP (App (App (Val (GoInstruction (GoLoad (go.GoType.FunctionType (go.signature.Signature
          [go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse.ty] false [go.bool])))))
          (Val #sendWatch_ptr)) (Val #wv)) {{ Ψ }}) $$ []
  · iintro !> %rcv %D %wv %Ψ Hres HA Htt Hst HS Hmu Htrue Hfalse
    as_aux_lemma =>
      watch_resp
  iclear sendWatch
  ihave HLI : iprop(∃ (rcv : List mvcc.api.WResp) (cs : List Loc) (D : List v3rpc.WatchRespM),
      "Hst" ∷ v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs D ∗
      "Hcons" ∷ spscConsumer r.γctrl cs ∗ "Hwc" ∷ mvcc.api.wsRecv r.ι rcv ∗
      "HA" ∷ monoListAuthOwn r.γr 1 rcv ∗ "Htt" ∷ v3rpc.sendTok r ∗
      "HS" ∷ v3rpc.sendSt r idsL pendL rcv D) $$ [Hst Hcons Hwc HA Htt Hids Hpend]
  · iexists [], [], []
    iframe Hst Hcons Hwc HA Htt
    iunfold v3rpc.sendSt
    iexists [], (fun _ => []), ∅, ∅, ∅
    iframe Hids Hpend
    isplitr
    · ipureintro
      refine ⟨v3rpc.sendInv_nil _, rfl, fun _ _ => rfl, fun X _ => by simp [v3rpc.idLive, GMap.lookup_empty],
        v3rpc.sendHist_nil _ _, fun X _ h => by simp [GMap.lookup_empty] at h⟩
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iintro !>; iapply BigSepM.bigSepM_empty.2; itrivial
    iunfold v3rpc.rcvOk
    iintro !> %n %x %h
    simp at h
  -- the loop's postcondition: it returns (`sendRet`), then the deferred function runs
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := v3rpc.sendRet r pendL)) $$ [- HΦ Hdefer]
  rotate_left
  · iintro %v Hv
    iunfold v3rpc.sendRet at Hv
    icases Hv with ⟨%Hv, Hret⟩
    subst Hv
    iunfold v3rpc.retSt at Hret
    icases Hret with ⟨%rcv', %rcv, %pend, %PM, Hwc, Htt, HPM, #Hpsl⟩
    as_aux_lemma =>
      send_return
  wp_for HLI
  (try simp only [_root_.decide_true, ↓reduceIte])
  (try wp_auto)
  wp_apply +noauto (hCh r.W.γm r.ι) $$ [] as %ch' %Hch'
  · iframe #
  subst Hch'
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `wresp, ok := <-sws.watchStream.Chan()`
    simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse, inferInstance, inferInstance,
      inferInstance, inferInstance, mvcc.api.wsChanOf r.ι, mvcc.api.wsChanNames r.ι
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hch
    iapply Hrecvb $$ Hwc
    iintro %wv %okw Hres
    cases okw
    · simp only [Bool.false_eq_true, ↓reduceIte]
      irename Hres => Hwc
      wp_auto
      ret_exit
    simp only [↓reduceIte]
    -- `sendWatch(wresp)` (`HsW`)
    wp_auto
    wp_bind (App (App (Val (GoInstruction (GoLoad _))) (Val #sendWatch_ptr)) _)
    iapply HsW $$ Hres HA Htt Hst HS Hmu [-] []
    · iintro %x %Dn ⟨Hst, Hwc, HA, Htt, HS, Hmu⟩
      wp_auto
      wp_for_post
      iframe
      iexists rcv ++ [x], cs, Dn
      iframe
    · iintro Hret
      wp_auto
      ret_exit
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `c, ok := <-sws.ctrlStream`
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, r.ctrl, r.γctrl.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iapply spsc_rcv_au r.γctrl r.ctrl (v3rpc.ctrlP r ci) (fun _ => iprop(True)) cs _ $$ Hspsc
      [$Hlc1 $Hlc2] Hcons
    inext
    iintro %cl %okc Hres
    cases okc
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hres with ⟨-, %Hz⟩
      wp_auto
      ret_exit
    simp only [↓reduceIte]
    icases Hres with ⟨HP, Hcons⟩
    iunfold v3rpc.ctrlP at HP
    icases HP with ⟨%m, #Hmsg, %Hm, Hco⟩
    iunfold v3rpc.ctrlOk at Hco
    icases Hco with ⟨%ireq, %req, #Hupat, %Hans, Hcw, Hat⟩
    wp_auto
    -- `if c.Created`: the watch responses queued before it go first (unit W-K)
    ihave #Hmsg0 := Hmsg
    iunfold v3rpc.watchRespMsg at Hmsg0
    icases Hmsg0 with ⟨%Hln0, %hh0, %esl0, %eps0, -, -, -, #HfCr0, -, -, -, -, -, -, -, -⟩
    wp_auto
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := v3rpc.ctrlMid r ci sws idsL pendL req m)) $$ [Hst Hwc HA Htt HS Hmu Hcw]
    rotate_left
    · -- after the `if` (`ctrlMid`): the rest of the control case, or the drain's return
      iintro %v Hv
      iunfold v3rpc.ctrlMid at Hv
      icases Hv with (⟨%Hv, %rcv, %D, Hst, Hwc, HA, Htt, HS, Hmu, Hcw, #Hord⟩ | ⟨%Hv, Hret⟩)
      · subst Hv
        as_aux_lemma =>
          wp_auto
          ctrl_rest
      · subst Hv
        wp_auto
        ret_exit
    cases hcr0 : m.created
    · try simp only [hcr0, Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      ihave #Hord : v3rpc.createdAfter r D.length m $$ []
      · unfold v3rpc.createdAfter
        rw [hcr0]
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        itrivial
      ctrl_mid_exec
    · try simp only [hcr0, ↓reduceIte]
      (try wp_auto)
      -- the stamp to drain to (unit W-K): the created response's watcher's, or `0`
      ihave ⟨Hcw, %k0, #Hk0, #Hreg0⟩ : iprop(
          v3rpc.ctrlWatcher r (auth.ctxTokenOf (GoInterface.ok ci)) req m ∗
          ∃ k0 : Nat, mvcc.api.wsSentLb r.ι k0 ∗
            (if m.canceled then iprop(True) else
              iprop(∃ i : v3rpc.RegInfo, v3rpc.regIs r.γreg m.watchId i ∗ ⌜i.k = k0⌝))) $$ [Hcw]
      · cases hca0 : m.canceled
        · have hreq : ∃ c, req = .create c := by
            rcases req with c | id | _ | _
            · exact ⟨c, rfl⟩
            all_goals (unfold v3rpc.ctrlAnswers at Hans; simp_all)
          obtain ⟨c, hreq⟩ := hreq
          irevert Hcw; rw [hreq]; iintro Hcw
          icases v3rpc.ctrlWatcher_reg hP r (auth.ctxTokenOf (GoInterface.ok ci)) c m hca0 $$ Hcw
            with ⟨Hcw, %i, #Hreg, #Hk⟩
          irevert Hcw; rw [← hreq]; iintro Hcw
          iframe Hcw
          iexists i.k
          iframe Hk
          simp only [Bool.false_eq_true, ↓reduceIte]
          iexists i
          iframe Hreg
          ipureintro; rfl
        · -- a refused create: nothing to say (`createdAfter` is `True`), the drain all the same
          iframe Hcw
          iexists 0
          isplitr
          · iapply hZero
          simp only [↓reduceIte]
          itrivial
      drain_created
      cases hca0 : m.canceled
      · -- `createdAfter`: the received list, at least the stamp, every `-1` among it sent
        isimp only [Bool.false_eq_true, ↓reduceIte] at Hreg0
        icases Hreg0 with ⟨%i, #Hreg, %Hik⟩
        ihave ⟨Hst, #HlbD⟩ := v3rpc.srvSendTok_lb _ _ $$ Hst
        icases persistent_entails_right (v3rpc.sendSt_neg1 r idsL pendL rcv D) $$ HS with ⟨%Hneg, HS⟩
        ihave #Hord : v3rpc.createdAfter r D.length m $$ []
        · unfold v3rpc.createdAfter
          rw [hcr0, hca0]
          simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
          iexists i, rcv, D
          iframe Hreg Hrs
          isplitr
          · ihave #Hlb' := HlbD
            iunfold v3rpc.downLb at Hlb'
            iexact Hlb'
          ipureintro; exact ⟨by rw [Hik]; exact Hkrcv, rfl, Hneg⟩
        ctrl_mid_exec
      · ihave #Hord : v3rpc.createdAfter r D.length m $$ []
        · unfold v3rpc.createdAfter
          rw [hca0]
          simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          itrivial
        ctrl_mid_exec
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-progressTicker.C`
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %tv -
    wp_auto
    wp_apply time.wp_Now as %tm -
    wp_apply sync.RWMutex.wp_Lock_guard (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) $$ []
      as ⟨Hlk, HP⟩
    · iframe #
    iunfold v3rpc.swsMu at HP
    icases HP with ⟨%PM, %VM, %FM, HPm, HVm, HFm, %HVF⟩
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range_mut (fun _ _ => iprop(∃ (o : Bool) (iv : w64), "ok" ∷ ok_ptr ↦ o ∗
        "id" ∷ id_ptr ↦ iv ∗ "Htt" ∷ v3rpc.sendTok r)) _ _ _ r.pm PM
      $$ HPm
    iintro %keys %Hkeys
    isplitl [ok id Htt]
    · iexists _, _; iframe
    isplitr
    · iintro !> %i %X %b %m' ⟨%Hk, %Hb, %Hag⟩ HP Hm
      icases HP with ⟨%o, %iv, ok, id, Htt⟩
      wp_auto
      wp_if_destruct
      rotate_left
      · (try wp_auto)
        icases Htt with ⟨Htt, Hrdr⟩
        wp_apply (hRP r.W.γm r.ι X) $$ [$Htt $Hrdr] as ⟨Htt, Hrdr⟩
        · iframe #
        ihave Htt : v3rpc.sendTok r $$ [Htt Hrdr]
        · unfold v3rpc.sendTok; iframe
        (try wp_auto)
        wp_apply (wp_mapInsert go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty r.pm m' X true) $$ [$Hm]
          as Hm
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        isplitl [ok id Htt]
        · iexists _, _; iframe
        ipureintro; intro k hk
        exact GMap.lookup_insert_ne _ _ (Ne.symm hk)
      · (try wp_auto)
        wp_apply (wp_mapInsert go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty r.pm m' X true) $$ [$Hm]
          as Hm
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        isplitl [ok id Htt]
        · iexists _, _; iframe
        ipureintro; intro k hk
        exact GMap.lookup_insert_ne _ _ (Ne.symm hk)
    iintro %m' HP Hm
    icases HP with ⟨%o, %iv, ok, id, Htt⟩
    wp_auto
    wp_apply sync.RWMutex.wp_Unlock_guard (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm)
      $$ [$Hlk Hm HVm HFm]
    · iframe #
      inext
      iunfold v3rpc.swsMu
      iexists m', VM, FM
      iframe
      ipureintro; exact HVF
    wp_apply time.wp_Since as %du -
    wp_apply hSec du as %fs -
    observe hs4 Ho4
    wp_auto
    wp_for_post
    iframe
    iexists rcv, cs, D
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-sws.closec`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, r.cc, r.γcc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hcc
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hcc
    iintro -
    wp_auto
    ret_exit
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
