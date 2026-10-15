/-
Proof of the spec of the same name (the watch slice's unit W-S): the send loop. The order of the
mvcc responses it sends is `WatchSendModel`'s (`SendInv`, `send_claim_direct`,
`send_claim_flush`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__sendLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__newResponseHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.GetProgressReportInterval
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isClientCtxErr
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__RequestProgress
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Assert
public import Spec.time.NewTicker
public import Spec.time.Ticker__Stop
public import Spec.time.Since
public import Spec.time.Duration__Seconds
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchSendModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchRecv

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A slice of buffered responses** (persistent): `sl` holds the responses `ls`, the `i`th the
response the send loop made of the mvcc response at index `P[i]` of those received `rcv` (with the
server's header, its revision the response's). -/
def v3rpc.pendSl (r : v3rpc.WRun GF) (rcv : List mvcc.RespM) (P : List Nat) (sl : GoSlice) :
    IProp GF :=
  iprop(∃ (ls : List Loc) (xs : List (mvcc.RespM × HdrM)), sl ↦*□ ls ∗
    ⌜ls.length = xs.length ∧ P.map (fun n => rcv[n]?) = xs.map (fun p => some p.1) ∧
      ∀ p ∈ xs, p.2.clusterId = r.srv.cid ∧ p.2.memberId = r.srv.mid ∧ p.2.revision = p.1.rev⌝ ∗
    [∗list] q ∈ ls.zip xs, v3rpc.watchRespMsg q.1 (v3rpc.mvccResp q.2.1 q.2.2))

instance v3rpc.pendSl_persistent (r : v3rpc.WRun GF) (rcv : List mvcc.RespM) (P : List Nat)
    (sl : GoSlice) : Persistent (v3rpc.pendSl r rcv P sl) := by
  unfold v3rpc.pendSl; infer_instance

/-- **What the send loop knows of the responses it received** (persistent): each is `respOk`, and
the responses received for its watcher up to it are `watchRecvOk`. -/
def v3rpc.rcvOk (γ : mvcc.WsNames) (rcv : List mvcc.RespM) : IProp GF :=
  iprop(□ ∀ (n : Nat) (x : mvcc.RespM), ⌜rcv[n]? = some x⌝ -∗
    mvcc.respOk x ∗ mvcc.watchRecvOk γ x.w ((rcv.take (n + 1)).filter (fun y => decide (y.w = x.w))))

instance v3rpc.rcvOk_persistent (γ : mvcc.WsNames) (rcv : List mvcc.RespM) :
    Persistent (v3rpc.rcvOk (GF := GF) γ rcv) := by
  unfold v3rpc.rcvOk; infer_instance

/-- **The send loop's state** of the mvcc responses `rcv` received with the responses `D` sent:
`WatchSendModel`'s invariant (`SendInv`) over the indices `S` sent and `pend` buffered, the ids
announced `IM` (the map `ids`), the mvcc responses sent being those of `S` in order, the buffered
responses (the map `pending`, `PM`). -/
def v3rpc.sendSt (r : v3rpc.WRun GF) (idsL pendL : Loc) (rcv : List mvcc.RespM)
    (D : List v3rpc.WatchRespM) : IProp GF :=
  iprop(∃ (S : List Nat) (pend : w64 → List Nat) (IM : GMap w64 Unit) (PM : GMap w64 GoSlice),
    ⌜v3rpc.SendInv rcv S pend (fun X => (IM !! X).isSome) none ∧
      D.filterMap v3rpc.WatchRespM.src = S.filterMap (fun m => rcv[m]?) ∧
      ∀ X, PM !! X = none → pend X = []⌝ ∗
    ownMap idsL (DFrac.own 1) IM ∗ ownMap pendL (DFrac.own 1) PM ∗
    ([∗map] _X ↦ sl ∈ PM, ownSliceCap Loc sl (DFrac.own 1)) ∗
    ([∗map] X ↦ sl ∈ PM, v3rpc.pendSl r rcv (pend X) sl) ∗
    v3rpc.rcvOk r.srv.γ rcv)

/-- A watcher's fixed fields determine its id (`mvcc.watcherFixed_agree`'s, without the mvcc
package's assumptions). -/
theorem v3rpc.watcherFixed_id (w : Loc) (r r' : mvcc.WatchRange) (fcs fcs' : GoSlice) :
    mvcc.watcherFixed (GF := GF) w r fcs ∗ mvcc.watcherFixed w r' fcs' ⊢ ⌜r.id = r'.id⌝ := by
  unfold mvcc.watcherFixed
  iintro ⟨⟨%Hn, %ks, %es, -, -, -, -, -, Hi, -⟩, ⟨-, %ks', %es', -, -, -, -, -, Hi', -⟩⟩
  icombine Hi Hi' gives %Hi
  ipureintro; exact Hi

/-- A watcher's responses with events carry one id (`respOk`'s, through `watcherFixed_agree`). -/
theorem v3rpc.rcvOk_same (γ : mvcc.WsNames) (rcv : List mvcc.RespM) :
    v3rpc.rcvOk (GF := GF) γ rcv ⊢ ⌜∀ (m1 m2 : Nat) (x1 x2 : mvcc.RespM), rcv[m1]? = some x1 →
      rcv[m2]? = some x2 → x1.w = x2.w → x1.evs ≠ [] → x2.evs ≠ [] → x1.id = x2.id⌝ := by
  refine (forall_intro fun m1 => ?_).trans pure_forall.2
  refine (forall_intro fun m2 => ?_).trans pure_forall.2
  refine (forall_intro fun x1 => ?_).trans pure_forall.2
  refine (forall_intro fun x2 => ?_).trans pure_forall.2
  by_cases h : rcv[m1]? = some x1 ∧ rcv[m2]? = some x2 ∧ x1.w = x2.w ∧ x1.evs ≠ [] ∧ x2.evs ≠ []
  · obtain ⟨h1, h2, hw, he1, he2⟩ := h
    iintro #H
    iunfold v3rpc.rcvOk at H
    ihave ⟨#Ho1, -⟩ := H $$ %m1 %x1 %h1
    ihave ⟨#Ho2, -⟩ := H $$ %m2 %x2 %h2
    iunfold mvcc.respOk at Ho1
    iunfold mvcc.respOk at Ho2
    icases Ho1 with ⟨-, %rr1, %f1, #Hf1, %Hid1⟩
    icases Ho2 with ⟨-, %rr2, %f2, #Hf2, %Hid2⟩
    irevert Hf1; rw [hw]; iintro #Hf1
    ihave %Hag := v3rpc.watcherFixed_id x2.w rr1 rr2 f1 f2 $$ [$Hf1 $Hf2]
    ipureintro
    intro _ _ _ _ _
    rw [Hid1 he1, Hid2 he2, Hag]
  · iintro _
    ipureintro
    intro a b c d e
    exact absurd ⟨a, b, c, d, e⟩ h

/-- A receipt: the response's facts (`watch_recv_au`'s) extend `rcvOk`. -/
theorem v3rpc.rcvOk_snoc (γ : mvcc.WsNames) (rcv : List mvcc.RespM) (r : mvcc.RespM) :
    v3rpc.rcvOk (GF := GF) γ rcv ∗ mvcc.respOk r ∗
      mvcc.watchRecvOk γ r.w ((rcv ++ [r]).filter (fun x => decide (x.w = r.w))) ⊢
      v3rpc.rcvOk γ (rcv ++ [r]) := by
  iintro ⟨#H, #Ho, #Hw⟩
  iunfold v3rpc.rcvOk at H
  iunfold v3rpc.rcvOk
  iintro !> %n %x %hx
  rcases Nat.lt_or_ge n rcv.length with hl | hl
  · rw [List.getElem?_append_left hl] at hx
    rw [List.take_append_of_le_length (by omega)]
    iapply H $$ %n %x %hx
  · have hn : n = rcv.length := by
      rcases Nat.lt_or_ge n (rcv.length + 1) with h' | h'
      · omega
      · rw [List.getElem?_eq_none (by simp; omega)] at hx; cases hx
    subst hn
    rw [List.getElem?_append_right (Nat.le_refl _)] at hx
    simp at hx
    subst hx
    rw [show rcv.length + 1 = (rcv ++ [r]).length by simp, List.take_length]
    iframe Ho Hw

/-- Buffered responses read the same after a receipt. -/
theorem v3rpc.pendSl_snoc (r : v3rpc.WRun GF) (rcv : List mvcc.RespM) (x : mvcc.RespM)
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
theorem v3rpc.pendMaps_delete (r : v3rpc.WRun GF) (rcv : List mvcc.RespM) (pend : w64 → List Nat)
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

end defs

set_option hygiene false in
/-- **The send loop's return** (any `return` of the loop): the deferred function stops the
ticker, drains the mvcc stream's channel (`watchConsumer`) and reports the buffered responses
(`pending`, from `sendSt`). -/
local macro "send_return" : tactic => `(tactic| (
  wp_for_post
  (try wp_auto)
  (try wp_for_post)
  wp_apply hStop tk $$ []
  · iexact Htk
  rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchStream.ty)
    (m := go!"Chan")]
  wp_call
  wp_auto
  ihave Hdr : iprop(∃ (rcv' : List mvcc.RespM) (v : go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse),
      "Hwc" ∷ mvcc.watchConsumer r.γc rcv' ∗ "ws" ∷ ws_ptr ↦ v) $$ [Hwc ws]
  · iexists _, _; iframe
  wp_for Hdr
  simp only [_root_.decide_true, ↓reduceIte]
  wp_auto
  wp_apply mvcc.wp_watch_receive r.srv.γ r.ch r.γc rcv' $$ Hch Hchinv Hwc
  iintro %wv %okw Hres
  cases okw
  · simp only [mvcc.watchRecvResult, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_for_post
    try iunfold v3rpc.sendSt at HS
    try icases HS with ⟨%S, %pend, %IM, %PM, %HSI, HIM, HPM, Hcaps, #Hpsl, #Hrok⟩
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
      · have Hif' : sint.Z j < sint.Z sl.len := of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
        have Hlen1 := Hlsl.1
        obtain ⟨l, hl⟩ : ∃ l, ls[(sint.Z j).toNat]? = some l :=
          ⟨_, List.getElem?_eq_getElem (by word)⟩
        obtain ⟨xp, hxp⟩ : ∃ xp, xs[(sint.Z j).toNat]? = some xp :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hxs.1]; word)⟩
        have hz : (ls.zip xs)[(sint.Z j).toNat]? = some (l, xp) := by
          rw [List.getElem?_zip_eq_some]; exact ⟨hl, hxp⟩
        ihave #Hm := BigSepL.bigSepL_lookup
          (Φ := fun _ q => v3rpc.watchRespMsg (GF := GF) q.1 (v3rpc.mvccResp q.2.1 q.2.2)) hz $$ Hmsgs
        iunfold v3rpc.watchRespMsg at Hm
        icases Hm with ⟨%Hln, %h, %esl, %eps, -, -, -, -, -, -, -, -, #HEv, -⟩
        have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj, Hif'⟩
        simp only [Hbnd, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index sl (sint.Z j) ls DFrac.discard l Hj $$ [] as -
        · iframe Hls; ipureintro; exact hl
        wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) _)
        iapply Hrep
        · itrivial
        iintro !> -
        wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; word
      · have Hf : (#(decide (sint.Z j < sint.Z sl.len)) : val) = #false := by
          revert Hif; cases decide (sint.Z j < sint.Z sl.len) <;> intro Hif
          · rfl
          · exact absurd rfl Hif
        rw [show decide ((#(decide (sint.Z j < sint.Z sl.len)) : val) = #false) = true from
          decide_eq_true Hf]
        simp only [↓reduceIte]
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _; iexact wrs
    iintro - HPM
    wp_auto
    iapply HΦ
    itrivial
  simp only [mvcc.watchRecvResult, ↓reduceIte]
  icases Hres with ⟨%x, Hwc, -⟩
  wp_auto
  wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) _)
  iapply Hrep
  · itrivial
  iintro !> -
  wp_auto
  wp_for_post
  iframe
  iexists _, _
  iframe))

set_option hygiene false in
/-- The store's reader slot `HR` as the watch params' (`P.R`), for a call of the mvcc stream. -/
local macro "to_params" : tactic => `(tactic| (
  ihave HR : (v3rpc.wParams r.srv).R $$ [HR]
  · unfold v3rpc.wParams mvcc.storeWatchParams; iexact HR))

set_option hygiene false in
/-- Back from the watch params' reader slot. -/
local macro "from_params" : tactic => `(tactic| (
  ihave HR : mvcc.watchReader r.srv.wsl r.srv.E.s r.srv.γ $$ [HR]
  · iexact HR))

set_option hygiene false in
/-- `h.Observe(x)` of a histogram whose `Observe` returns (`Ho`). -/
local macro "observe" h:term:max Ho:ident : tactic => `(tactic| (
  wp_bind (App (Val #(methods ($h).ty go!"Observe" ($h).v)) _)
  iapply $Ho:ident
  · itrivial
  iintro !> -))

set_option hygiene false in
/-- **A failed send** (`serr != nil`, from `Send`'s error case `Hne`): the context's error and
`isClientCtxErr` choose the log, then the loop returns (`send_return`). -/
local macro "send_fail" : tactic => `(tactic| (
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
  wp_apply +noauto HErrU $$ [] as %cerr -
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
    iintro %lsl -
    wp_auto
    wp_apply hCV cvF _ as %cnt ⟨%cnti, %Hcnt, #Hcs⟩
    subst Hcnt
    iunfold prometheus.counterSpec at Hcs
    wp_apply Hcs
    (try wp_auto)
    send_return
  · wp_apply hZE as %f -
    wp_apply wp_slice_literal (l := [f])
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hZD r.srv.lg _ _ $$ []
    · iframe #; ipureintro; exact Hnn.2
    (try wp_auto)
    send_return))

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
/-- **A created response for `X` sent**: `X` announced (`ids[X]`), its buffered responses
flushed in order (`send_claim_flush`), `pending[X]` deleted. -/
local macro "ctrl_created" X:term : tactic => `(tactic| (
  iunfold v3rpc.sendSt at HS
  icases HS with ⟨%S, %pend, %IM, %PM, %HSI, HIM, HPM, Hcaps, #Hpsl, #Hrok⟩
  obtain ⟨hI, hD, hPM⟩ := HSI
  wp_apply (wp_mapInsert go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty idsL IM $X ()) $$ HIM
    as HIM
  have hids : (fun Y => ((<[$X := ()]> IM) !! Y).isSome) =
      v3rpc.upd (fun Y => (IM !! Y).isSome) $X true := by
    funext Y; unfold v3rpc.upd; by_cases h : Y = $X
    · subst h; simp [GMap.lookup_insert]
    · simp [h, Ne.symm h]
  have hI1 := v3rpc.sendInv_created $X hI
  rw [← hids] at hI1
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
  ihave %Hsame := v3rpc.rcvOk_same _ _ $$ Hrok
  ihave #Hrok' := Hrok
  iunfold v3rpc.rcvOk at Hrok'
  ihave HF : iprop(∃ (j : w64) (vv : Loc) (D' : List v3rpc.WatchRespM),
      "i" ∷ i_ptr ↦ j ∗ "v" ∷ v_ptr ↦ vv ∗
      "Hst" ∷ v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs D' ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ (sint.Z j).toNat ≤ (pend $X).length ∧
        v3rpc.SendInv rcv (S ++ (pend $X).take (sint.Z j).toNat)
          (v3rpc.upd pend $X ((pend $X).drop (sint.Z j).toNat))
          (fun Y => ((<[$X := ()]> IM) !! Y).isSome) (some $X) ∧
        D'.filterMap v3rpc.WatchRespM.src =
          (S ++ (pend $X).take (sint.Z j).toNat).filterMap (fun n => rcv[n]?)⌝) $$ [i v Hst]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by decide, by simp, ?_, ?_⟩
    · simp only [show sint.Z (W64 0) = 0 from rfl, Int.toNat_zero, List.take_zero, List.append_nil,
        List.drop_zero, v3rpc.upd_self]
      exact hI1
    · simp only [show sint.Z (W64 0) = 0 from rfl, Int.toNat_zero, List.take_zero, List.append_nil,
        List.filterMap_append, Hm.2.2, List.filterMap_cons_none, List.filterMap_nil]
      exact hD
  wp_for HF
  obtain ⟨Hj0, HjP, hIk, hDk⟩ := Hj
  wp_if_destruct
  · have Hif' : sint.Z j < sint.Z ((PM !! $X).getD (zero_val GoSlice)).len :=
      of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
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
      (Φ := fun _ q => v3rpc.watchRespMsg (GF := GF) q.1 (v3rpc.mvccResp q.2.1 q.2.2)) hz $$ Hmsgs
    ihave #Hml' := Hml
    iunfold v3rpc.watchRespMsg at Hml'
    icases Hml' with ⟨%Hln', %h', %esl', %eps', -, -, -, -, -, -, -, -, #HEv', -⟩
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ((PM !! $X).getD (zero_val GoSlice)).len := ⟨Hj0, Hif'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z j) ls DFrac.discard l Hj0 $$ [] as -
    · iframe Hls; ipureintro; exact hl
    (try wp_auto)
    wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) _)
    iapply Hrep
    · itrivial
    iintro !> -
    (try wp_auto)
    have hpk : (v3rpc.upd pend $X ((pend $X).drop (sint.Z j).toNat)) $X =
        n :: (pend $X).drop ((sint.Z j).toNat + 1) := by
      obtain ⟨_, hnk⟩ := List.getElem?_eq_some_iff.1 hn
      rw [v3rpc.upd_same, List.drop_eq_getElem_cons hkP, hnk]
    ihave ⟨Hst, #Hlb⟩ := v3rpc.srvSendTok_lb _ _ $$ Hst
    ihave HDn : r.Dn D'.length (v3rpc.mvccResp xp.1 xp.2) $$ []
    · iunfold v3rpc.watchStreamSpec at Hspec
      icases Hspec $$ %D'.length %(v3rpc.mvccResp xp.1 xp.2) with ⟨-, Hb⟩
      iapply Hb
      iunfold v3rpc.watchDn
      isplitr
      · ipureintro; exact ⟨hxpF.1, hxpF.2.1⟩
      iright
      iunfold v3rpc.mvccOk
      iexists xp.1, ((rcv.take (n + 1)).filter (fun y => decide (y.w = xp.1.w))), D'
      isplitr
      · ipureintro; exact ⟨rfl, hxpF.2.2, rfl, v3rpc.take_filter_getLast rcv hrn⟩
      isplitr
      · iunfold v3rpc.downLbW
        ihave #Hlb' := Hlb
        iunfold v3rpc.downLb at Hlb'
        iexact Hlb'
      isplitr
      · ihave ⟨-, #Hw⟩ := Hrok' $$ %n %xp.1 %hrn
        iexact Hw
      ipureintro
      intro hev
      obtain ⟨-, hc⟩ := v3rpc.send_claim_flush hIk hpk hrn hev Hsame
      unfold v3rpc.sentEvsOf
      rw [hDk]
      exact hc
    wp_bind (App (Val #(methods si.ty go!"Send" si.v)) (Val #l))
    iapply HSend $$ [Hst HDn]
    · iframe Hst HDn Hml
    iintro !> %serr Hsr
    icases Hsr with (⟨%Hserr, Hst⟩ | ⟨%Hne, #Hse, Hst⟩)
    rotate_left
    · send_fail
    subst Hserr
    wp_auto
    wp_for_post
    iframe
    have hj1 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
    iexists (j + W64 1), _, _
    iframe
    ipureintro
    have hk1 : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by rw [hj1]; omega
    rw [hk1, List.take_add_one, hn]
    simp only [Option.toList_some]
    refine ⟨by omega, by omega, ?_, ?_⟩
    · have := v3rpc.sendInv_flush hIk hpk
      rw [v3rpc.upd_upd] at this
      rw [← List.append_assoc]
      exact this
    · rw [List.filterMap_append, hDk, ← List.append_assoc, List.filterMap_append (l := S ++ _)]
      simp [v3rpc.mvccResp, hrn]
  · have hnl : ¬ sint.Z j < sint.Z ((PM !! $X).getD (zero_val GoSlice)).len := by
      intro h
      apply Hif
      rw [decide_eq_true h]
    simp only [hnl, decide_false, eq_self_iff_true, _root_.decide_true, ↓reduceIte]
    have Hlen1 := Hlsl.1
    have hkE : (sint.Z j).toNat = (pend $X).length := by rw [HlenP, ← Hxs.1] at HjP ⊢; word
    rw [hkE, List.take_length, List.drop_length] at hIk
    rw [hkE, List.take_length] at hDk
    wp_auto
    wp_apply (wp_mapDelete pendL PM $X go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
      (go.GoType.SliceType (go.GoType.PointerType etcdserverpb.WatchResponse.ty))) $$ HPM as HPM
    wp_apply time.wp_Since as %du -
    wp_apply hSec du as %fs -
    observe hs3 Ho3
    wp_auto
    wp_for_post
    iframe
    iexists rcv, cs ++ [cl], D'
    iframe
    iunfold v3rpc.sendSt
    iexists (S ++ pend $X), (v3rpc.upd pend $X []), (<[$X := ()]> IM), (GMap.delete $X PM)
    ihave ⟨Hcaps, Hpsl'⟩ := v3rpc.pendMaps_delete r rcv pend PM $X $$ [Hcaps Hpsl]
    · iframe Hcaps Hpsl
    iframe HIM HPM Hcaps Hpsl' Hrok
    ipureintro
    refine ⟨?_, hDk, ?_⟩
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

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem v3rpc.serverWatchStream.sendLoop.wp_proof
    (hHdr : v3rpc.serverWatchStream.newResponseHeader.spec (GF := GF) (hG := hG))
    (hGPI : v3rpc.GetProgressReportInterval.spec (GF := GF) (hG := hG))
    (hICE : v3rpc.isClientCtxErr.spec (GF := GF) (hG := hG))
    (hRP : mvcc.watchStream.RequestProgress.spec (GF := GF) (hG := hG))
    (hAssert : verify.Assert.spec (GF := GF) (hG := hG))
    (hNT : time.NewTicker.spec (GF := GF) (hG := hG))
    (hStop : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (hSince : time.Since.spec (GF := GF) (hG := hG))
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hZD : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hCV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    v3rpc.serverWatchStream.sendLoop.spec (GF := GF) (hG := hG) := by
  intro sws r
  wp_start as ⟨#Hsws, Hst, Hcons, Hwc, Hres, Hmu⟩
  ihave #Hsws' := Hsws
  iunfold v3rpc.swsIs at Hsws'
  icases Hsws' with ⟨%Hnn, #Flg, #Fcid, #Fmid, #Fmrb, #Fsg, #Fwa, #Fag, #Fst, #Fws, #Fctrl, #Fpm,
    #Fvm, #Ffm, #Fcc, #Hsrv, #Hstream, #Hspec, #Hup, #Hwstream, #Hwch, #Hch, #Hchinv, #Hspsc, #Hcc,
    #Hmug⟩
  ihave #Hsrv' := Hsrv
  iunfold v3rpc.watchSrvOk at Hsrv'
  icases Hsrv' with ⟨#Hwsto, %Hγst, #Hrso, #Hauth, #Hvars⟩
  ihave #Hvars' := Hvars
  iunfold v3rpc.watchVars at Hvars'
  icases Hvars' with ⟨#Heof, #HeInv, #HeOld, #HeEmpty, #HeDenied, #HeEWR, #HeDup, #HmCompacted,
    #HmInv, #HmOld, #HmEmpty, #HmDenied, #HmWC, #HstreamF, #Hh1, #Hh2, #Hh3, #Hh4, #Htracer,
    #Hcanc, #Hrep, #Hguard⟩
  iunfold v3rpc.reportEventOk at Hrep
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
  icases HstreamF with ⟨%cvF, #HcvF⟩
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
  iunfold v3rpc.sendRes at Hres
  icases Hres with ⟨HR, Hiv⟩
  (try wp_auto)
  wp_bind (App (Val wrapDefer) _)
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Unit) go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
    (go.StructType [])) as %idsL Hids
  wp_apply (wp_map_make1 (K := w64) (V := GoSlice) go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
    (go.GoType.SliceType (go.GoType.PointerType etcdserverpb.WatchResponse.ty))) as %pendL Hpend
  wp_apply hGPI $$ [$Hiv] as %d ⟨%Hd, Hiv⟩
  · iframe #
  wp_apply hNT d $$ [] as %tk #Htk
  · ipureintro; exact Hd
  ihave #Htk' := Htk
  iunfold time.isTicker at Htk'
  icases Htk' with ⟨-, %tch, %γt, #HC, #Hbag⟩
  ipersist sws
  ipersist ids
  ipersist pending
  ipersist progressTicker
  ihave Hinv : iprop(∃ (rcv : List mvcc.RespM) (cs : List Loc) (D : List v3rpc.WatchRespM),
      "Hst" ∷ v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs D ∗
      "Hcons" ∷ spscConsumer r.γctrl cs ∗ "Hwc" ∷ mvcc.watchConsumer r.γc rcv ∗
      "HS" ∷ v3rpc.sendSt r idsL pendL rcv D) $$ [Hst Hcons Hwc Hids Hpend]
  · iexists [], [], []
    iframe Hst Hcons Hwc
    iunfold v3rpc.sendSt
    iexists [], (fun _ => []), ∅, ∅
    iframe Hids Hpend
    isplitr
    · ipureintro
      refine ⟨v3rpc.sendInv_nil _, rfl, fun _ _ => rfl⟩
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    iunfold v3rpc.rcvOk
    iintro !> %n %x %h
    simp at h
  wp_for Hinv
  rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchStream.ty)
    (m := go!"Chan")]
  wp_call
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `wresp, ok := <-sws.watchStream.Chan()`
    simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse, inferInstance, inferInstance,
      inferInstance, inferInstance, r.ch, r.γc.ch
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hch
    iapply mvcc.watch_recv_au r.srv.γ r.ch r.γc rcv _ $$ Hchinv Hwc
    iintro %wv %okw Hres
    sorry
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `c, ok := <-sws.ctrlStream`
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, r.ctrl, r.γctrl.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iapply spsc_rcv_au r.γctrl r.ctrl (v3rpc.ctrlP r) (fun _ => iprop(True)) cs _ $$ Hspsc
      [$Hlc1 $Hlc2] Hcons
    inext
    iintro %cl %okc Hres
    cases okc
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hres with ⟨-, %Hz⟩
      wp_auto
      send_return
    simp only [↓reduceIte]
    icases Hres with ⟨HP, Hcons⟩
    iunfold v3rpc.ctrlP at HP
    icases HP with ⟨%m, #Hmsg, %Hm, #Hco⟩
    wp_auto
    wp_apply time.wp_Now as %tm -
    rw [Hsi]
    wp_auto
    ihave HDn : r.Dn D.length m $$ []
    · iunfold v3rpc.watchStreamSpec at Hspec
      icases Hspec $$ %D.length %m with ⟨-, Hb⟩
      iapply Hb
      iunfold v3rpc.watchDn
      isplitr
      · ipureintro; exact ⟨Hm.1, Hm.2.1⟩
      ileft
      iframe Hco
      ipureintro; exact Hm.2.2
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
      ihave #Hco' := Hco
      iunfold v3rpc.ctrlOk at Hco'
      icases Hco' with ⟨%ireq, %req, #Hupat, %Hans⟩
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
      cases hca : m.canceled <;> cases hcr : m.created
      · exfalso
        unfold v3rpc.ctrlAnswers at Hans
        rcases req with c | id | _ | _
        · rw [hcr] at Hans; exact absurd Hans.2.2.2.2.1 (by decide)
        · rw [hca] at Hans; exact absurd Hans.2.2.2.2.2.1 (by decide)
        · exact Hans.2.2.2.2.elim
        · exact Hans.2.2.2.2.elim
      case false.true =>
        wp_auto
        ctrl_assert
        ctrl_created m.watchId
      case true.false =>
        wp_auto
        ctrl_assert
        iunfold v3rpc.sendSt at HS
        icases HS with ⟨%S, %pend, %IM, %PM, %HSI, HIM, HPM, Hcaps, #Hpsl, #Hrok⟩
        obtain ⟨hI, hD, hPM⟩ := HSI
        have hD' : (D ++ [m]).filterMap v3rpc.WatchRespM.src = S.filterMap (fun n => rcv[n]?) := by
          rw [List.filterMap_append, hD]; simp [Hm.2.2]
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
          iexists S, pend, IM, PM
          iframe HIM HPM Hcaps Hpsl Hrok
          ipureintro
          exact ⟨hI, hD', hPM⟩
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
          iexists S, pend, (GMap.delete m.watchId IM), PM
          iframe HIM HPM Hcaps Hpsl Hrok
          ipureintro
          refine ⟨?_, hD', hPM⟩
          have hids : (fun Y => ((GMap.delete m.watchId IM) !! Y).isSome) =
              v3rpc.upd (fun Y => (IM !! Y).isSome) m.watchId false := by
            funext Y; unfold v3rpc.upd; by_cases h : Y = m.watchId
            · subst h; simp [GMap.lookup_delete]
            · simp [h, Ne.symm h]
          rw [hids]
          exact v3rpc.sendInv_cancel m.watchId hI
      case true.true =>
        rw [Hcc hca hcr]
        wp_auto
        ctrl_assert
        ctrl_created (W64 (-1))
    send_fail
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
        "id" ∷ id_ptr ↦ iv ∗ "HR" ∷ mvcc.watchReader r.srv.wsl r.srv.E.s r.srv.γ)) _ _ _ r.pm PM
      $$ HPm
    iintro %keys %Hkeys
    isplitl [ok id HR]
    · iexists _, _; iframe
    isplitr
    · iintro !> %i %X %b %m' ⟨%Hk, %Hb, %Hag⟩ HP Hm
      icases HP with ⟨%o, %iv, ok, id, HR⟩
      wp_auto
      wp_if_destruct
      rotate_left
      · (try wp_auto)
        to_params
        wp_apply hRP r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo X $$ [$HR] as HR
        · iframe #
        from_params
        (try wp_auto)
        wp_apply (wp_mapInsert go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty r.pm m' X true) $$ [$Hm]
          as Hm
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        isplitl [ok id HR]
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
        isplitl [ok id HR]
        · iexists _, _; iframe
        ipureintro; intro k hk
        exact GMap.lookup_insert_ne _ _ (Ne.symm hk)
    iintro %m' HP Hm
    icases HP with ⟨%o, %iv, ok, id, HR⟩
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
    send_return
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
