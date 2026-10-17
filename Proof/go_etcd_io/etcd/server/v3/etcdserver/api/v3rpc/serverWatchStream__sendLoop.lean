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
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Chan
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Assert
public import Spec.time.NewTicker
public import Spec.time.Ticker__Stop
public import Spec.time.Duration__Seconds
public import Spec.time.Duration__Seconds_ptr
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

/-- **What the send loop knows of the responses it received** (persistent): each is `respOk`, the
responses received for its watcher up to it are `watchRecvOk`, and what it says of the stream
(`mvccExtra`, unit W-M2). -/
def v3rpc.rcvOk (γs : v3rpc.StreamNames) (γ : mvcc.WsNames) (rcv : List mvcc.RespM) : IProp GF :=
  iprop(□ ∀ (n : Nat) (x : mvcc.RespM), ⌜rcv[n]? = some x⌝ -∗
    mvcc.respOk x ∗ mvcc.watchRecvOk γ x.w ((rcv.take (n + 1)).filter (fun y => decide (y.w = x.w))) ∗
    v3rpc.mvccExtra γs x)

instance v3rpc.rcvOk_persistent (γs : v3rpc.StreamNames) (γ : mvcc.WsNames) (rcv : List mvcc.RespM) :
    Persistent (v3rpc.rcvOk (GF := GF) γs γ rcv) := by
  unfold v3rpc.rcvOk; infer_instance

/-- **The send loop's state** of the mvcc responses `rcv` received with the responses `D` sent:
`WatchSendModel`'s invariant (`SendInv`) over the indices `S` sent and `pend` buffered, the ids
announced `IM` (the map `ids`), the mvcc responses sent being those of `S` in order, the buffered
responses (the map `pending`, `PM`); an id other than `-1` is announced exactly when it is live
after the responses sent (`idLive`, the watch slice's unit W-C). -/
def v3rpc.sendSt (r : v3rpc.WRun GF) (idsL pendL : Loc) (rcv : List mvcc.RespM)
    (D : List v3rpc.WatchRespM) : IProp GF :=
  iprop(∃ (S : List Nat) (pend : w64 → List Nat) (IM : GMap w64 Unit) (PM : GMap w64 GoSlice),
    ⌜v3rpc.SendInv rcv S pend (fun X => (IM !! X).isSome) none ∧
      D.filterMap v3rpc.WatchRespM.src = S.filterMap (fun m => rcv[m]?) ∧
      (∀ X, PM !! X = none → pend X = []) ∧
      ∀ X, X ≠ W64 (-1) → ((IM !! X).isSome = true ↔ v3rpc.idLive D X)⌝ ∗
    ownMap idsL (DFrac.own 1) IM ∗ ownMap pendL (DFrac.own 1) PM ∗
    ([∗map] _X ↦ sl ∈ PM, ownSliceCap Loc sl (DFrac.own 1)) ∗
    ([∗map] X ↦ sl ∈ PM, v3rpc.pendSl r rcv (pend X) sl) ∗
    v3rpc.rcvOk r.γs r.srv.γ rcv)

/-! ## Live ids (the watch slice's unit W-C) -/

/-- An mvcc response sent leaves every id's liveness as it was. -/
theorem v3rpc.idLive_snoc_src (D : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM)
    (h : m.src ≠ none) (X : w64) : v3rpc.idLive (D ++ [m]) X ↔ v3rpc.idLive D X := by
  unfold v3rpc.idLive
  simp [List.filter_append, h]

/-- A control response sent decides its own id's liveness. -/
theorem v3rpc.idLive_snoc_ctrl (D : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM)
    (h : m.src = none) (X : w64) :
    v3rpc.idLive (D ++ [m]) X ↔
      (if m.watchId = X then (m.created && !m.canceled) = true else v3rpc.idLive D X) := by
  unfold v3rpc.idLive
  by_cases hx : m.watchId = X
  · simp [List.filter_append, h, hx]
  · simp [List.filter_append, h, hx]

/-- The announced ids after a created response for `X` is sent (`ids[X]` set): live. -/
theorem v3rpc.idsLive_created (D : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM)
    (IM : GMap w64 Unit) (X : w64) (hsrc : m.src = none) (hX : m.watchId = X)
    (hL : ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ v3rpc.idLive D Y))
    (hok : X ≠ W64 (-1) → (m.created && !m.canceled) = true) :
    ∀ Y, Y ≠ W64 (-1) → (((<[X := ()]> IM) !! Y).isSome = true ↔ v3rpc.idLive (D ++ [m]) Y) := by
  intro Y hY
  rw [v3rpc.idLive_snoc_ctrl _ _ hsrc]
  by_cases h : Y = X
  · subst h; simp [GMap.lookup_insert, hX, hok hY]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]
    simp only [hX, Ne.symm h, ↓reduceIte]
    exact hL Y hY

/-- The announced ids after a canceled response for `X ≠ -1` is sent (`ids[X]` deleted). -/
theorem v3rpc.idsLive_canceled (D : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM)
    (IM : GMap w64 Unit) (X : w64) (hsrc : m.src = none) (hX : m.watchId = X)
    (hc : m.canceled = true)
    (hL : ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ v3rpc.idLive D Y)) :
    ∀ Y, Y ≠ W64 (-1) →
      (((GMap.delete X IM) !! Y).isSome = true ↔ v3rpc.idLive (D ++ [m]) Y) := by
  intro Y hY
  rw [v3rpc.idLive_snoc_ctrl _ _ hsrc]
  by_cases h : Y = X
  · subst h; simp [GMap.lookup_delete, hX, hc]
  · rw [GMap.lookup_delete_ne _ (Ne.symm h)]
    simp only [hX, Ne.symm h, ↓reduceIte]
    exact hL Y hY

/-- The announced ids after a control response for `-1` is sent: as they were. -/
theorem v3rpc.idsLive_neg1 (D : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM)
    (IM : GMap w64 Unit) (hsrc : m.src = none) (hX : m.watchId = W64 (-1))
    (hL : ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ v3rpc.idLive D Y)) :
    ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ v3rpc.idLive (D ++ [m]) Y) := by
  intro Y hY
  rw [v3rpc.idLive_snoc_ctrl _ _ hsrc]
  have : m.watchId ≠ Y := by rw [hX]; exact Ne.symm hY
  simp only [this, ↓reduceIte]
  exact hL Y hY

/-- The announced ids after an mvcc response is sent: as they were. -/
theorem v3rpc.idsLive_src (D : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM)
    (IM : GMap w64 Unit) (hsrc : m.src ≠ none)
    (hL : ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ v3rpc.idLive D Y)) :
    ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ v3rpc.idLive (D ++ [m]) Y) := by
  intro Y hY
  rw [v3rpc.idLive_snoc_src _ _ hsrc]
  exact hL Y hY

/-- A pending index of `X` names a response of id `X`. -/
theorem v3rpc.pend_id {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {ex : Option w64} (hI : v3rpc.SendInv rcv S pend ids ex) {X : w64}
    {n : Nat} {t : List Nat} (hp : pend X = n :: t) {x : mvcc.RespM} (hx : rcv[n]? = some x) :
    x.id = X := by
  have hs := hI.split X
  have hm : n ∈ v3rpc.idxOf rcv X := by rw [hs, hp]; simp
  obtain ⟨-, hid⟩ := v3rpc.mem_idxOf hm
  obtain ⟨y, hy, hyX⟩ := v3rpc.idOf_eq_id hid
  rw [hx] at hy; cases hy; exact hyX

/-- A watcher's fixed fields determine its id (`mvcc.watcherFixed_agree`'s, without the mvcc
package's assumptions). -/
theorem v3rpc.watcherFixed_id (w : Loc) (r r' : mvcc.WatchRange) (fcs fcs' : GoSlice) :
    mvcc.watcherFixed (GF := GF) w r fcs ∗ mvcc.watcherFixed w r' fcs' ⊢ ⌜r.id = r'.id⌝ := by
  unfold mvcc.watcherFixed
  iintro ⟨⟨%Hn, %ks, %es, -, -, -, -, -, Hi, -⟩, ⟨-, %ks', %es', -, -, -, -, -, Hi', -⟩⟩
  icombine Hi Hi' gives %Hi
  ipureintro; exact Hi

/-- A watcher's responses with events carry one id (`respOk`'s, through `watcherFixed_agree`). -/
theorem v3rpc.rcvOk_same (γs : v3rpc.StreamNames) (γ : mvcc.WsNames) (rcv : List mvcc.RespM) :
    v3rpc.rcvOk (GF := GF) γs γ rcv ⊢ ⌜∀ (m1 m2 : Nat) (x1 x2 : mvcc.RespM), rcv[m1]? = some x1 →
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
theorem v3rpc.rcvOk_snoc (γs : v3rpc.StreamNames) (γ : mvcc.WsNames) (rcv : List mvcc.RespM)
    (r : mvcc.RespM) :
    v3rpc.rcvOk (GF := GF) γs γ rcv ∗ mvcc.respOk r ∗
      mvcc.watchRecvOk γ r.w ((rcv ++ [r]).filter (fun x => decide (x.w = r.w))) ∗
      v3rpc.mvccExtra γs r ⊢
      v3rpc.rcvOk γs γ (rcv ++ [r]) := by
  iintro ⟨#H, #Ho, #Hw, #Hx⟩
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
    iframe Ho Hw Hx

/-- **Every received response of id `-1` was sent** (unit W-K): the send loop never buffers one
(`SendInv.noPend` at `-1`), so it is among the sent ones (`hD`). -/
theorem v3rpc.neg1_sent {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {D : List v3rpc.WatchRespM} (hI : v3rpc.SendInv rcv S pend ids none)
    (hD : D.filterMap v3rpc.WatchRespM.src = S.filterMap (fun n => rcv[n]?)) :
    ∀ x ∈ rcv, x.id = W64 (-1) → ∃ m' ∈ D, m'.src = some x := by
  intro x hx hid
  obtain ⟨n, hn, hnx⟩ := List.getElem_of_mem hx
  have hin : n ∈ v3rpc.idxOf rcv (W64 (-1)) := by
    unfold v3rpc.idxOf; rw [List.mem_filter]
    refine ⟨List.mem_range.2 hn, ?_⟩
    unfold v3rpc.idOf; simp [List.getElem?_eq_getElem hn, hnx, hid]
  have hp : pend (W64 (-1)) = [] := hI.noPend _ (Or.inr rfl) (by simp)
  rw [hI.split, hp, List.append_nil, List.mem_filter] at hin
  have hmem : x ∈ S.filterMap (fun n => rcv[n]?) :=
    List.mem_filterMap.2 ⟨n, hin.1, by simp [List.getElem?_eq_getElem hn, hnx]⟩
  rw [← hD] at hmem
  obtain ⟨m', hm', hsrc⟩ := List.mem_filterMap.1 hmem
  exact ⟨m', hm', hsrc⟩

/-- **What a received response says of the stream** (unit W-M2): with the stream's auxiliary
name and its progress fact `progQ` saved at the mvcc stream's `prog` (the channel's), a response
received on the mvcc channel with its registration fact (`chanRegFact`: its watcher's id, one the
stream assigned) and, for id `-1`, the channel's progress fact, is `mvccExtra` (a later away: the
saved propositions agree a step later; `progQ` is timeless). -/
theorem v3rpc.mvccExtra_of_recv (γs : v3rpc.StreamNames) (γo : mvcc.WsStreamNames) (γa : GName)
    (γc : mvcc.WatchChanNames) (x : mvcc.RespM) (h : γo.ids = γc.ids ∧ γo.prog = γc.prog) :
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ savedPropOwn γo.prog DFrac.discard (v3rpc.progQ γs) ∗
      mvcc.respOk x ∗ mvcc.chanRegFact γc x.w ∗ (⌜x.id = W64 (-1)⌝ → mvcc.progFact γc.prog) ⊢
      ◇ v3rpc.mvccExtra γs x := by
  iintro ⟨#Haux, #Hsp, #Hok, #Hrf, #Hpf⟩
  ihave #HI : □ (⌜x.evs ≠ []⌝ -∗ ∃ (γo' : mvcc.WsStreamNames) (γa' : GName),
      streamAuxIs γs (v3rpc.auxOf γo' γa') ∗ mvcc.idAssigned γo' x.id x.w) $$ []
  · iintro !> %hne
    iexists γo, γa
    iframe Haux
    iunfold mvcc.respOk at Hok
    icases Hok with ⟨-, %rr, %fcs, #Hf, %Hid⟩
    iunfold mvcc.chanRegFact at Hrf
    icases Hrf with ⟨%rr', %fcs', #Hf', #Hida, -⟩
    ihave %Hag := v3rpc.watcherFixed_id x.w rr rr' fcs fcs' $$ [$Hf $Hf']
    unfold mvcc.idAssigned
    iunfold mvcc.chanIdAssigned at Hida
    rw [h.1, Hid hne, Hag]
    iexact Hida
  by_cases hx : x.id = W64 (-1)
  · ihave #Hp := Hpf $$ %hx
    iunfold mvcc.progFact at Hp
    icases Hp with ⟨%Q, #HQs, #HQ⟩
    irevert Hsp; rw [h.2]; iintro #Hsp
    ihave Heq := saved_prop_agree γc.prog _ _ Q (v3rpc.progQ γs) $$ HQs Hsp
    ihave Hl : ▷ v3rpc.progQ γs $$ [Heq]
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨H1, -⟩
      iapply H1
      iexact HQ
    imod Hl with #Hq
    imodintro
    iunfold v3rpc.mvccExtra
    iframe HI
    iintro !> -
    iexact Hq
  · imodintro
    iunfold v3rpc.mvccExtra
    iframe HI
    iintro !> %h'
    exact absurd h' hx

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
theorem v3rpc.pendMaps_insert (r : v3rpc.WRun GF) (rcv : List mvcc.RespM) (pend : w64 → List Nat)
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
theorem v3rpc.pendSls_snoc (r : v3rpc.WRun GF) (rcv : List mvcc.RespM) (x : mvcc.RespM)
    (pend : w64 → List Nat) (PM : GMap w64 GoSlice) :
    ([∗map] Y ↦ sl ∈ PM, v3rpc.pendSl (GF := GF) r rcv (pend Y) sl) ⊢
      [∗map] Y ↦ sl ∈ PM, v3rpc.pendSl r (rcv ++ [x]) (pend Y) sl :=
  BigSepM.bigSepM_mono fun {_ _} _ => v3rpc.pendSl_snoc r rcv x _ _

open Iris.ProofMode in
/-- **Every received response of id `-1` was sent** (unit W-K), from the send state. -/
theorem v3rpc.sendSt_neg1 (r : v3rpc.WRun GF) (idsL pendL : Loc) (rcv : List mvcc.RespM)
    (D : List v3rpc.WatchRespM) :
    v3rpc.sendSt r idsL pendL rcv D ⊢ ⌜∀ x ∈ rcv, x.id = W64 (-1) → ∃ m' ∈ D, m'.src = some x⌝ := by
  iintro HS
  iunfold v3rpc.sendSt at HS
  icases HS with ⟨%S, %pend, %IM, %PM, %HSI, -, -, -, -, -⟩
  obtain ⟨hI, hD, -, -⟩ := HSI
  ipureintro; exact v3rpc.neg1_sent hI hD

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
  (try simp only [_root_.decide_true, ↓reduceIte])
  (try wp_auto)
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
/-- **A received mvcc watch response, sent or buffered** (the `sendWatch` closure, inlined: the
loop's `watchStream.Chan()` case and the drain before a `Created` response, unit W-K), from the
receive (`Hres`) to the invariant of the loop it ends in: the main loop's (`rcv`, `cs`, `D`) or the
drain's (`rcv`, `D`, `drained`): `k` gives the loop's witnesses for the responses sent `Dn`. -/
local macro "watch_resp" k:tactic : tactic => `(tactic| (
  icases Hres with ⟨%x, Hwc, #HrI, #HrO, #HrW, #HrF, #HrP⟩
  -- what the response says of the stream (unit W-M2)
  imod v3rpc.mvccExtra_of_recv r.γs r.γo r.γa r.γc x ⟨Hγoc.1, Hγoc.2.1⟩ $$ [Haux Hsp HrO HrF HrP]
    with #HrX
  · iframe Haux Hsp HrO HrF HrP
  iunfold v3rpc.sendSt at HS
  icases HS with ⟨%S, %pend, %IM, %PM, %HSI, HIM, HPM, Hcaps, #Hpsl, #Hrok⟩
  obtain ⟨hI, hD, hPM, hL⟩ := HSI
  ihave #Hrok2 := v3rpc.rcvOk_snoc _ _ _ _ $$ [Hrok HrO HrW HrX]
  · iframe Hrok HrO HrW HrX
  ihave #HrI' := HrI
  iunfold mvcc.respIs at HrI'
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
  wp_apply hHdr sws r wv.Revision' as %hh ⟨%tt, %ll, #Hhdr⟩
  · iframe #
  (try wp_auto)
  irename «$r0» => Hwr
  ihave %Hwrn := typedPointsto_not_null _ _ _ $$ Hwr
  ipersist Hwr
  have hCR : wv.CompactRevision' = W64 0 := HwvI.2.2
  ihave #Hmsg : v3rpc.watchRespMsg «$r0_ptr»
      (v3rpc.mvccResp x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩) $$ []
  · iapply (v3rpc.watchRespMsg_intro «$r0_ptr»
      (etcdserverpb.WatchResponse.mk _ hh wv.WatchID' false (!decide (wv.CompactRevision' = W64 0))
        wv.CompactRevision' [] false esl slice.nil 0)
      (v3rpc.mvccResp x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩) ps
      (by simp [v3rpc.mvccResp, HwvI.1]) rfl (by simp [v3rpc.mvccResp, hCR])
      (by simp [v3rpc.mvccResp, hCR]) rfl rfl (by simp [v3rpc.mvccResp, Hpsl]))
    simp only [v3rpc.mvccResp]
    iframe Hwr Hhdr Hesl
    isplitr
    · ipureintro; exact Hwrn
    iexact Hevs
  rw [HwvI.1]
  by_cases hd : ((IM !! x.id).isSome = true ∨ x.id = W64 (-1))
  · by_cases h1 : x.id = W64 (-1)
    all_goals (
      simp only [h1, _root_.decide_true, decide_false, Bool.not_true, Bool.not_false, ↓reduceIte]
      (try wp_auto)
      first
      | (have hIMs : (IM !! wv.WatchID').isSome = true := (by rw [HwvI.1]; exact hd.resolve_right h1); wp_apply (wp_map_lookup2 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty (go.StructType []) idsL IM wv.WatchID' (DFrac.own 1)) $$ HIM as HIM; simp only [hIMs, _root_.decide_true, Bool.not_true, ↓reduceIte]; (try wp_auto))
      | skip
      wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) _)
      iapply Hrep
      · itrivial
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
      ihave %Hsame := v3rpc.rcvOk_same _ _ _ $$ Hrok2
      ihave HDn : r.Dn D.length (v3rpc.mvccResp x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩) $$ []
      · iunfold v3rpc.watchStreamSpec at Hspec
        icases Hspec $$ %D.length %(v3rpc.mvccResp x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩)
          with ⟨-, Hb⟩
        iapply Hb
        iunfold v3rpc.watchDn
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        iright
        iunfold v3rpc.mvccOk
        iexists x, ((rcv ++ [x]).filter (fun y => decide (y.w = x.w))), D
        isplitr
        · ipureintro
          refine ⟨rfl, HwvI.2.1, rfl, ?_, fun hn => (hL _ hn).1 (hd.resolve_right hn)⟩
          simp [List.filter_append]
        isplitr
        · iunfold v3rpc.downLbW
          ihave #Hlb' := Hlb
          iunfold v3rpc.downLb at Hlb'
          iexact Hlb'
        isplitr
        · iexact HrW
        isplitr
        rotate_left
        · iexact HrX
        ipureintro
        intro hev
        have hc := v3rpc.send_claim_direct hI hd hev Hsame
        rw [v3rpc.filterMap_snoc_bound _ _ _ hI.bound] at hc
        unfold v3rpc.sentEvsOf
        rw [hD]
        exact hc
      wp_bind (App (Val #(methods si.ty go!"Send" si.v)) (Val #«$r0_ptr»))
      iapply HSend $$ [Hst HDn]
      · iframe Hst HDn Hmsg
      iintro !> %serr Hsr
      icases Hsr with (⟨%Hserr, Hst⟩ | ⟨%Hne, #Hse, Hst⟩)
      rotate_left
      · send_fail
      subst Hserr
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Lock_guard (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) $$ []
        as ⟨Hlk, HP⟩
      · iframe #
      iunfold v3rpc.swsMu at HP
      icases HP with ⟨%PM3, %VM3, %FM3, HPm, HVm, HFm, %HVF3⟩
      (try wp_auto)
      by_cases hl : sint.Z (W64 0) < sint.Z wv.Events'.len
      · simp only [hl, _root_.decide_true, ↓reduceIte]
        (try wp_auto)
        wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool r.pm PM3
          wv.WatchID' _) $$ HPm as HPm
        cases hb : (PM3 !! wv.WatchID').getD false
        · (try wp_auto)
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
          wp_for_post
          iframe
          obtain ⟨Dn, hDn⟩ : ∃ Dn : List v3rpc.WatchRespM, Dn = D ++ [v3rpc.mvccResp x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩] := ⟨_, rfl⟩
          $k
          subst hDn
          iframe
          iunfold v3rpc.sendSt
          iexists S ++ [rcv.length], pend, IM, PM
          ihave #Hpsl2 := v3rpc.pendSls_snoc r rcv x pend PM $$ Hpsl
          iframe HIM HPM Hcaps Hpsl2 Hrok2
          ipureintro
          refine ⟨v3rpc.sendInv_recv_direct hI hd, ?_, hPM,
            v3rpc.idsLive_src _ _ _ (by simp [v3rpc.mvccResp]) hL⟩
          rw [List.filterMap_append, hD, List.filterMap_append, v3rpc.filterMap_snoc_bound _ _ _ hI.bound]
          simp [v3rpc.mvccResp]
        · (try wp_auto)
          wp_apply (wp_mapInsert go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty r.pm PM3
            wv.WatchID' false) $$ HPm as HPm
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
          wp_for_post
          iframe
          obtain ⟨Dn, hDn⟩ : ∃ Dn : List v3rpc.WatchRespM, Dn = D ++ [v3rpc.mvccResp x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩] := ⟨_, rfl⟩
          $k
          subst hDn
          iframe
          iunfold v3rpc.sendSt
          iexists S ++ [rcv.length], pend, IM, PM
          ihave #Hpsl2 := v3rpc.pendSls_snoc r rcv x pend PM $$ Hpsl
          iframe HIM HPM Hcaps Hpsl2 Hrok2
          ipureintro
          refine ⟨v3rpc.sendInv_recv_direct hI hd, ?_, hPM,
            v3rpc.idsLive_src _ _ _ (by simp [v3rpc.mvccResp]) hL⟩
          rw [List.filterMap_append, hD, List.filterMap_append, v3rpc.filterMap_snoc_bound _ _ _ hI.bound]
          simp [v3rpc.mvccResp]
      · simp only [hl, decide_false, ↓reduceIte]
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
        wp_for_post
        iframe
        obtain ⟨Dn, hDn⟩ : ∃ Dn : List v3rpc.WatchRespM, Dn = D ++ [v3rpc.mvccResp x ⟨r.srv.cid, r.srv.mid, wv.Revision', tt, ll⟩] := ⟨_, rfl⟩
        $k
        subst hDn
        iframe
        iunfold v3rpc.sendSt
        iexists S ++ [rcv.length], pend, IM, PM
        ihave #Hpsl2 := v3rpc.pendSls_snoc r rcv x pend PM $$ Hpsl
        iframe HIM HPM Hcaps Hpsl2 Hrok2
        ipureintro
        refine ⟨v3rpc.sendInv_recv_direct hI hd, ?_, hPM,
            v3rpc.idsLive_src _ _ _ (by simp [v3rpc.mvccResp]) hL⟩
        rw [List.filterMap_append, hD, List.filterMap_append, v3rpc.filterMap_snoc_bound _ _ _ hI.bound]
        simp [v3rpc.mvccResp])
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
    wp_for_post
    iframe
    obtain ⟨Dn, hDn⟩ : ∃ Dn : List v3rpc.WatchRespM, Dn = D := ⟨_, rfl⟩
    $k
    subst hDn
    iframe
    iunfold v3rpc.sendSt
    iexists S, v3rpc.upd pend x.id (pend x.id ++ [rcv.length]), IM, (<[x.id := sl']> PM)
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
      iexact Hmsg
    ihave ⟨Hcaps, Hpsl3⟩ := v3rpc.pendMaps_insert r (rcv ++ [x]) pend PM x.id sl'
      (pend x.id ++ [rcv.length]) $$ [Hcaps Hcap']
    · iframe Hcaps Hcap' Hpsl2 Hnew
    iframe HIM HPM Hcaps Hpsl3 Hrok2
    ipureintro
    refine ⟨v3rpc.sendInv_recv_pend hI (by simpa using hd), ?_, ?_, hL⟩
    · rw [v3rpc.filterMap_snoc_bound _ _ _ hI.bound]; exact hD
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
  icases HS with ⟨%S, %pend, %IM, %PM, %HSI, HIM, HPM, Hcaps, #Hpsl, #Hrok⟩
  obtain ⟨hI, hD, hPM, hL⟩ := HSI
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
  ihave %Hsame := v3rpc.rcvOk_same _ _ _ $$ Hrok
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
          (S ++ (pend $X).take (sint.Z j).toNat).filterMap (fun n => rcv[n]?) ∧
        ∀ Y, Y ≠ W64 (-1) → (((<[$X := ()]> IM) !! Y).isSome = true ↔ v3rpc.idLive D' Y)⌝)
        $$ [i v Hst]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by decide, by simp, ?_, ?_, hL1⟩
    · simp only [show sint.Z (W64 0) = 0 from rfl, Int.toNat_zero, List.take_zero, List.append_nil,
        List.drop_zero, v3rpc.upd_self]
      exact hI1
    · simp only [show sint.Z (W64 0) = 0 from rfl, Int.toNat_zero, List.take_zero, List.append_nil,
        List.filterMap_append, Hm.2.2, List.filterMap_cons_none, List.filterMap_nil]
      exact hD
  wp_for HF
  obtain ⟨Hj0, HjP, hIk, hDk, hLk⟩ := Hj
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
      · ipureintro
        exact ⟨rfl, hxpF.2.2, rfl, v3rpc.take_filter_getLast rcv hrn,
          fun hn => (hLk _ hn).1 (by rw [v3rpc.pend_id hIk hpk hrn]; simp [GMap.lookup_insert])⟩
      isplitr
      · iunfold v3rpc.downLbW
        ihave #Hlb' := Hlb
        iunfold v3rpc.downLb at Hlb'
        iexact Hlb'
      ihave ⟨-, #HwN, #HxN⟩ := Hrok' $$ %n %xp.1 %hrn
      isplitr
      · iexact HwN
      isplitr
      rotate_left
      · iexact HxN
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
    refine ⟨by omega, by omega, ?_, ?_, v3rpc.idsLive_src _ _ _ (by simp [v3rpc.mvccResp]) hLk⟩
    · have := v3rpc.sendInv_flush hIk hpk
      rw [v3rpc.upd_upd] at this
      rw [← List.append_assoc]
      exact this
    · rw [List.filterMap_append, hDk, ← List.append_assoc, List.filterMap_append (l := S ++ _)]
      simp [v3rpc.mvccResp, hrn]
  · have hnl : ¬ sint.Z j < sint.Z ((PM !! $X).getD (zero_val GoSlice)).len := by
      first
      | exact Hif
      | (intro h; apply Hif; rw [decide_eq_true h])
    (try simp only [hnl, decide_false, eq_self_iff_true, _root_.decide_true, ↓reduceIte])
    have Hlen1 := Hlsl.1
    have hkE : (sint.Z j).toNat = (pend $X).length := by rw [HlenP, ← Hxs.1] at HjP ⊢; word
    rw [hkE, List.take_length, List.drop_length] at hIk
    rw [hkE, List.take_length] at hDk
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
    iexists (S ++ pend $X), (v3rpc.upd pend $X []), (<[$X := ()]> IM), (GMap.delete $X PM)
    ihave ⟨Hcaps, Hpsl'⟩ := v3rpc.pendMaps_delete r rcv pend PM $X $$ [Hcaps Hpsl]
    · iframe Hcaps Hpsl
    iframe HIM HPM Hcaps Hpsl' Hrok
    ipureintro
    refine ⟨?_, hDk, ?_, hLk⟩
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
/-- The drain's invariant after a response it sent or buffered (`watch_resp`'s exit; not drained,
`hdr0`). -/
local macro "drain_exit" : tactic => `(tactic| (
  iexists rcv ++ [x], Dn, dr
  isplitr
  · ipureintro; intro hd; rw [hdr0] at hd; cases hd
  isplitr
  · rw [hdr0]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial))

set_option hygiene false in
/-- **The drain before a created response** (unit W-K): the watch responses queued on the
channel are sent (`watch_resp`) until a non-blocking receive finds it empty
(`watch_tryrecv_au_alt`), which shows that every response sent on the channel by then was
received, so the received list `rcv` extends the snapshot `l0` (`Hl0`); after the loop, `Hdl`. -/
local macro "drain_created" : tactic => `(tactic| (
  ihave HId : iprop(∃ (rcv : List mvcc.RespM) (D : List v3rpc.WatchRespM) (dr : Bool),
      "%Hdl" ∷ ⌜dr = true → l0 <+: rcv⌝ ∗
      "#Hrs" ∷ (if dr then mvcc.chanSentLb r.γc rcv else iprop(True)) ∗
      "Hst" ∷ v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs D ∗
      "Hwc" ∷ mvcc.watchConsumer r.γc rcv ∗ "HS" ∷ v3rpc.sendSt r idsL pendL rcv D ∗
      "drained" ∷ drained_ptr ↦ dr) $$ [Hst Hwc HS drained]
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
    wp_apply +noauto hChan r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo
      as %ch' ⟨-, #Hch'⟩
    · iframe #
    icombine Hwch Hch' gives %Hcheq
    subst Hcheq
    wp_auto
    wp_bind (App (Val (GoInstruction SelectStmt)) _)
    iapply (chan.wp_select_nonblocking_alt [iprop(⌜l0 <+: rcv⌝ ∗ mvcc.chanSentLb r.γc rcv)] _ _ _ _)
      $$ [] [-] []
    all_goals first | iNamedAccu | skip
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro __CTX
      iNamed __CTX
      simp only [chan.nonblockingAltClausePre]
      iexists go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse, inferInstance, inferInstance,
        inferInstance, inferInstance, r.ch, r.γc.ch
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hch
      iapply mvcc.watch_tryrecv_au_alt r.srv.γ r.ch r.γc rcv l0 _ _ Hγoc.2.2.2 $$ Hchinv Hwc Hl0
      isplit
      · iintro %wv %okw Hres
        cases okw
        · simp only [mvcc.watchRecvResult, Bool.false_eq_true, ↓reduceIte]
          irename Hres => Hwc
          wp_auto
          send_return
        simp only [mvcc.watchRecvResult, ↓reduceIte]
        watch_resp drain_exit
      · iintro Hwc %Hpre #Hsnap
        iframe
        iframe #
        ipureintro; exact Hpre
    · iintro __CTX Hnr
      iNamed __CTX
      icases (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hnr with ⟨%Hpre, #Hsnap⟩
      wp_auto
      wp_for_post
      iframe
      iexists rcv, D, true
      isplitr
      · ipureintro; intro _; exact Hpre
      isplitr
      · simp only [↓reduceIte]; iexact Hsnap
      iframe
  wp_if_destruct
  rotate_left
  · exfalso; cases dr <;> simp_all
  have hdr1 : dr = true := by cases dr <;> simp_all
  have Hl0rcv : l0 <+: rcv := Hdl hdr1
  irevert Hrs; rw [hdr1]; simp only [↓reduceIte]; iintro #Hrs))

set_option hygiene false in
/-- **The rest of the control case** (from `start := time.Now()`), after the drain of a `Created`
response or without it (unit W-K). -/
local macro "ctrl_rest" : tactic => `(tactic| (
  wp_apply time.wp_Now as %tm -
  rw [Hsi]
  wp_auto
  ihave HDn : r.Dn D.length m $$ [Hcw Hat]
  · iunfold v3rpc.watchStreamSpec at Hspec
    icases Hspec $$ %D.length %m with ⟨-, Hb⟩
    iapply Hb
    iunfold v3rpc.watchDn
    isplitr
    · ipureintro; exact ⟨Hm.1, Hm.2.1⟩
    ileft
    isplitr
    · ipureintro; exact Hm.2.2
    isplitl [Hcw Hat]
    · iunfold v3rpc.ctrlOk
      iexists ireq, req, γo, γa
      iframe Hauxc Hupat Hcw Hat
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
      have hX : m.watchId = m.watchId := rfl
      have hok : m.watchId ≠ W64 (-1) → (m.created && !m.canceled) = true :=
        fun _ => by simp [hca, hcr]
      ctrl_created m.watchId
    case true.false =>
      wp_auto
      ctrl_assert
      iunfold v3rpc.sendSt at HS
      icases HS with ⟨%S, %pend, %IM, %PM, %HSI, HIM, HPM, Hcaps, #Hpsl, #Hrok⟩
      obtain ⟨hI, hD, hPM, hL⟩ := HSI
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
        exact ⟨hI, hD', hPM, v3rpc.idsLive_neg1 _ _ _ Hm.2.2 hw hL⟩
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
        refine ⟨?_, hD', hPM, v3rpc.idsLive_canceled _ _ _ _ Hm.2.2 rfl hca hL⟩
        have hids : (fun Y => ((GMap.delete m.watchId IM) !! Y).isSome) =
            v3rpc.upd (fun Y => (IM !! Y).isSome) m.watchId false := by
          funext Y; unfold v3rpc.upd; by_cases h : Y = m.watchId
          · subst h; simp [GMap.lookup_delete]
          · simp [h, Ne.symm h]
        rw [hids]
        exact v3rpc.sendInv_cancel m.watchId hI
    case true.true =>
      have hX : m.watchId = W64 (-1) := Hcc hca hcr
      have hok : W64 (-1) ≠ W64 (-1) → (m.created && !m.canceled) = true :=
        fun h => absurd rfl h
      rw [Hcc hca hcr]
      wp_auto
      ctrl_assert
      ctrl_created (W64 (-1))
  send_fail))

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
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hSecP : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (hZD : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hCV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hChan : mvcc.watchStream.Chan.spec (GF := GF) (hG := hG)) :
    v3rpc.serverWatchStream.sendLoop.spec (GF := GF) (hG := hG) := by
  intro sws r
  wp_start as ⟨#Hsws, Hst, Hcons, Hwc, Hres, Hmu⟩
  ihave #Hsws' := Hsws
  iunfold v3rpc.swsIs at Hsws'
  icases Hsws' with ⟨%Hnn, #Flg, #Fcid, #Fmid, #Fmrb, #Fsg, #Fwa, #Fag, #Fst, #Fws, #Fctrl, #Fpm,
    #Fvm, #Ffm, #Fcc, #Hsrv, #Hstream, #Hspec, #Haux, #Hup, #Hwstream, #Hwch, #Hch, #Hchinv, #Hspsc, #Hcc,
    #Hmug, %Hγoc, #Hsp, -⟩
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
      refine ⟨v3rpc.sendInv_nil _, rfl, fun _ _ => rfl, fun X _ => by simp [v3rpc.idLive, GMap.lookup_empty]⟩
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    iunfold v3rpc.rcvOk
    iintro !> %n %x %h
    simp at h
  wp_for Hinv
  wp_apply +noauto hChan r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo as %ch' ⟨-, #Hch'⟩
  · iframe #
  icombine Hwch Hch' gives %Hcheq
  subst Hcheq
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
    cases okw
    · simp only [mvcc.watchRecvResult, Bool.false_eq_true, ↓reduceIte]
      irename Hres => Hwc
      wp_auto
      send_return
    simp only [mvcc.watchRecvResult, ↓reduceIte]
    watch_resp (iexists rcv ++ [x], cs, Dn)
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
    icases HP with ⟨%m, #Hmsg, %Hm, Hco⟩
    iunfold v3rpc.ctrlOk at Hco
    icases Hco with ⟨%ireq, %req, %γo, %γa, #Hauxc, #Hupat, %Hans, Hcw, Hat⟩
    wp_auto
    -- `if c.Created`: the watch responses queued before it go first (unit W-K)
    ihave #Hmsg0 := Hmsg
    iunfold v3rpc.watchRespMsg at Hmsg0
    icases Hmsg0 with ⟨%Hln0, %hh0, %esl0, %eps0, -, -, -, #HfCr0, -, -, -, -, -, -, -, -⟩
    wp_auto
    cases hcr0 : m.created
    · try simp only [hcr0, Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      ihave #Hord : v3rpc.createdAfter r.γs D.length m $$ []
      · unfold v3rpc.createdAfter
        rw [hcr0]
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        itrivial
      ctrl_rest
    · try simp only [hcr0, ↓reduceIte]
      (try wp_auto)
      -- the snapshot to drain past (unit W-K): the created response's, or the empty one
      ihave %Hag : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf r.γo r.γa⌝) $$ []
      · iapply streamAuxIs_agree
        isplit
        · iexact Hauxc
        · iexact Haux
      obtain ⟨hγo, -⟩ := v3rpc.auxOf_inj Hag
      cases hca0 : m.canceled
      · have hreq : ∃ c, req = .create c := by
          rcases req with c | id | _ | _
          · exact ⟨c, rfl⟩
          all_goals (unfold v3rpc.ctrlAnswers at Hans; simp_all)
        obtain ⟨c, hreq⟩ := hreq
        irevert Hcw; rw [hreq]; iintro Hcw
        icases v3rpc.ctrlWatcher_snap r.srv.γ γo c m hca0 $$ Hcw with ⟨Hcw, %w0, %l0, #Hia0, #Hl0s⟩
        irevert Hcw; rw [← hreq]; iintro Hcw
        ihave #Hl0 : mvcc.chanSentLb r.γc l0 $$ []
        · iapply (mvcc.chanSentLb_stream γo r.γc l0 (by rw [hγo]; exact Hγoc.2.2.1)).2 $$ Hl0s
        drain_created
        -- `createdAfter`: the received list as the later snapshot
        ihave ⟨Hst, #HlbD⟩ := v3rpc.srvSendTok_lb _ _ $$ Hst
        icases persistent_entails_right (v3rpc.sendSt_neg1 r idsL pendL rcv D) $$ HS with ⟨%Hneg, HS⟩
        ihave #Hord : v3rpc.createdAfter r.γs D.length m $$ []
        · unfold v3rpc.createdAfter
          rw [hcr0, hca0]
          simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
          iexists γo, γa, w0, l0, rcv, D
          iframe Hauxc Hia0 Hl0s
          isplitr
          · iapply (mvcc.chanSentLb_stream γo r.γc rcv (by rw [hγo]; exact Hγoc.2.2.1)).1 $$ Hrs
          isplitr
          · iunfold v3rpc.downLbW
            ihave #Hlb' := HlbD
            iunfold v3rpc.downLb at Hlb'
            iexact Hlb'
          ipureintro; exact ⟨Hl0rcv, rfl, Hneg⟩
        ctrl_rest
      · -- a refused create: nothing to say (`createdAfter` is `True`), the drain all the same
        imod (monoListLbOwn_nil (GF := GF) (A := mvcc.RespM) r.γc.sentl) with #Hl0n
        obtain ⟨l0, hl0⟩ : ∃ l0 : List mvcc.RespM, l0 = [] := ⟨_, rfl⟩
        ihave #Hl0 : mvcc.chanSentLb r.γc l0 $$ []
        · rw [hl0]; unfold mvcc.chanSentLb; iexact Hl0n
        drain_created
        ihave #Hord : v3rpc.createdAfter r.γs D.length m $$ []
        · unfold v3rpc.createdAfter
          rw [hca0]
          simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          itrivial
        ctrl_rest
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
