/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__run.lean` (the watch slice's unit W-C).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.ReceiptTactics
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__run
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__nextResume
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__dispatchEvent
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__addSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__closeSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__joinSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatcherStreamBufLogger
public import Spec.go_etcd_io.etcd.client.v3.watchRequest__toPB
public import Spec.go_etcd_io.etcd.client.v3.progressRequest__toPB
public import Proof.go_etcd_io.etcd.client.v3.MapSplit
public import Spec.go_etcd_io.etcd.client.v3.watcher__closeStream
public import Spec.go_etcd_io.etcd.client.v3.isHaltErr
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Int64
public import Perennial.Proof.time
public import Proof.go_etcd_io.etcd.client.v3.WatchClientModel
public import Proof.go_etcd_io.etcd.client.v3.WatchContent
public import Proof.go_etcd_io.etcd.client.v3.WatchCompl
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client


namespace client
section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The answer of the request at up position `i` (the server's token, held by `run`). -/
def ansH (γs : StreamNames) (i : Nat) : IProp GF :=
  iprop(∃ (γo : mvcc.WsStreamNames) (γa : GName),
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ v3rpc.ansTok γa i)

/-- The token of the registered watch id `X` (the server's, held by `run`). -/
def idH (γs : StreamNames) (X : w64) : IProp GF :=
  iprop(∃ (γo : mvcc.WsStreamNames) (γa : GName),
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ mvcc.idTok γo X)

/-- What `run` keeps of a received response (persistent): an mvcc response's facts. -/
def respInfo (m : v3rpc.WatchRespM) : IProp GF :=
  match m.src with
  | some ρ => mvcc.respOk ρ
  | none => iprop(True)

instance respInfo_persistent (m : v3rpc.WatchRespM) : Persistent (respInfo (GF := GF) m) := by
  unfold respInfo; split <;> infer_instance

/-- The create request of a watch. -/
abbrev createOfP (P : WsPrm GF) : v3rpc.CreateReqM := createOf P.key P.ed P.rev P.pn P.sr

/-- **A registered substream's place on the channel** (persistent; K2e-7d): a snapshot `l` of the
stream's channel's sent list from its created response (taken after the registration, at an index
`n` at most its length), whose responses of id `-1` were all sent down before the created one
(among `L`). -/
def regSnap (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (w : Loc) : IProp GF :=
  iprop(∃ (γo : mvcc.WsStreamNames) (γa : GName) (l : List mvcc.RespM) (L : List v3rpc.WatchRespM)
      (n : Nat),
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ mvcc.streamSentLb γo l ∗
    mvcc.streamRegAt γo w n ∗
    ⌜n ≤ l.length ∧ L <+: Dm ∧ ∀ x ∈ l, x.id = W64 (-1) → ∃ m' ∈ L, m'.src = some x⌝)

instance regSnap_persistent (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (w : Loc) :
    Persistent (regSnap (GF := GF) γs Dm w) := by
  unfold regSnap; infer_instance

/-- **A registered substream's watcher** (persistent): the mvcc watcher `w` the server registered
for its create at the id `X` (range `rg`, no filters, first revision `lo`; K2e-7d: registered
with the create's start-read flag, its place on the channel), the id assigned to it. -/
def regFacts (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF) (X : w64)
    (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) : IProp GF :=
  iprop(⌜v3rpc.createRangeOk (createOfP P) X rg⌝ ∗ mvcc.watcherIs V.R.γ w rg fcs lo ∗
    fcs ↦*□ ([] : List GoFunc) ∗
    (∃ γw : mvcc.WatcherNames, mvcc.watcherMeta V.R.γ w γw ∗ ⌜γw.sr = P.sr⌝) ∗ regSnap γs Dm w ∗
    ∃ (γo : mvcc.WsStreamNames) (γa : GName), streamAuxIs γs (v3rpc.auxOf γo γa) ∗
      mvcc.idAssigned γo X w)

instance regFacts_persistent (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (P : WsPrm GF) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) :
    Persistent (regFacts V γs Dm P X w rg fcs lo) := by
  unfold regFacts; infer_instance

/-- `regFacts` over more responses. -/
theorem regFacts_mono (V : WEnv GF) (γs : StreamNames) {Dm Dm' : List v3rpc.WatchRespM}
    (P : WsPrm GF) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
    (hp : Dm <+: Dm') : regFacts V γs Dm P X w rg fcs lo ⊢ regFacts V γs Dm' P X w rg fcs lo := by
  unfold regFacts regSnap
  iintro ⟨%H1, #H2, #H3, #H4, ⟨%γo, %γa, %l, %L, %n, #Ha, #Hl, #Hn, %Hp⟩, #H6⟩
  iframe H2 H3 H4 H6
  isplitr
  · ipureintro; exact H1
  iexists γo, γa, l, L, n
  iframe Ha Hl Hn
  ipureintro; exact ⟨Hp.1, Hp.2.1.trans hp, Hp.2.2⟩

/-- The events of the watcher `w` received so far (`Dm`), in order. -/
abbrev evsSoFar (Dm : List v3rpc.WatchRespM) (w : Loc) : List mvcc.EvM :=
  ((v3rpc.sentEvsOf Dm w).map mvcc.RespM.evs).flatten

/-- **The dispatch cursor** `hi` of a registered substream (persistent): the last event's revision
dispatched so far (`rev - 1` if none), the events so far a cut of the watcher's events of a
sealed log. -/
def cursorOk (V : WEnv GF) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM) (w : Loc)
    (rg : mvcc.WatchRange) (lo : Nat) (hi : w64) : IProp GF :=
  iprop(⌜(evsSoFar Dm w = [] ∧ hi = P.rev - W64 1) ∨
      (∃ e, (evsSoFar Dm w).getLast? = some e ∧ hi = e.kv.modRev)⌝ ∗
    (⌜evsSoFar Dm w = []⌝ ∨ ∃ (L1 : mvcc.Log) (d1 : Nat), mvcc.idxSealed V.R.γ.st.idx L1 ∗
      ⌜evsSoFar Dm w = mvcc.watchEvents L1 rg lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length⌝))

instance cursorOk_persistent (V : WEnv GF) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM) (w : Loc)
    (rg : mvcc.WatchRange) (lo : Nat) (hi : w64) : Persistent (cursorOk V P Dm w rg lo hi) := by
  unfold cursorOk; infer_instance

/-- **The second dispatch cursor of a registered substream** (K2e-7d; `sent` the responses
dispatched): `γh2`'s positions `C2`, and, unless the watch promises no completeness or the
substream stopped, one more than the responses, the last the cursor (`cur2Ok`). -/
def cur2St (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF) (X : w64)
    (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc) : IProp GF :=
  iprop(∃ C2 : List w64, monoListAuthOwn P.γh2 1 C2 ∗
    (⌜P.γ.cpl = false⌝ ∨ dghostVar P.γx DFrac.discard true ∨
      ⌜C2.length = sent.length + 1⌝ ∗ ∃ c2 : w64, ⌜C2.getLast? = some c2⌝ ∗
        cur2Ok V γs P Dm X w rg lo c2))

/-- `cur2St` over more responses, none of the watcher's events. -/
theorem cur2St_mono (V : WEnv GF) (γs : StreamNames) {Dm Dm' : List v3rpc.WatchRespM}
    (P : WsPrm GF) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc)
    (h : evsOf Dm' w = evsOf Dm w) (hp : Dm <+: Dm') :
    cur2St V γs Dm P X w rg lo sent ⊢ cur2St V γs Dm' P X w rg lo sent := by
  unfold cur2St
  iintro ⟨%C2, Ha, (%H | #H | ⟨%H, %c2, %Hl, #Hc⟩)⟩
  · iexists C2; iframe Ha; ileft; ipureintro; exact H
  · iexists C2; iframe Ha; iright; ileft; iexact H
  · iexists C2; iframe Ha; iright; iright
    isplitr
    · ipureintro; exact H
    iexists c2
    isplitr
    · ipureintro; exact Hl
    iapply cur2Ok_mono V γs P X w rg lo c2 h hp $$ Hc

/-- **What `run` holds of a substream in its phase** (but its id field). -/
def wsRest (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF) :
    WPh → IProp GF
  | .queued si => iprop(spscProducer P.γr ([] : List Loc) ∗
      monoListAuthOwn P.γhi 1 [P.rev - W64 1] ∗ monoListAuthOwn P.γh2 1 [P.rev - W64 1] ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} P.rev ∗
      (match si with
       | some i => v3rpc.upAtW γs i (.create (createOfP P))
       | none => iprop(True)))
  | .reg X => iprop(∃ (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
      (sent : List Loc) (C : List w64),
      regFacts V γs Dm P X w rg fcs lo ∗ spscProducer P.γr sent ∗ monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ ∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P Dm w rg lo hi) ∗
      cur2St V γs Dm P X w rg lo sent)
  | _ => iprop(True)

/-- **A registered substream's id was never cancelled, unless it stopped** (persistent; unit W-K):
no cancel request for its id `X` was sent (`S.L`), or its goroutine has stopped (`γx`: `run`
cancels a registered id only after a dispatch to it failed). -/
def noCancelOk (S : RunSt) (P : WsPrm GF) : WPh → IProp GF
  | .reg X => iprop(⌜∀ i : Nat, S.L[i]? ≠ some (v3rpc.WatchReqM.cancel X)⌝ ∨
      dghostVar P.γx DFrac.discard true)
  | _ => iprop(True)

instance noCancelOk_persistent (S : RunSt) (P : WsPrm GF) (ph : WPh) :
    Persistent (noCancelOk (GF := GF) S P ph) := by
  cases ph <;> unfold noCancelOk <;> infer_instance

/-- `noCancelOk` across a step that sends no cancel request for the substream's id. -/
theorem noCancelOk_mono {S S' : RunSt} (P : WsPrm GF) (ph : WPh)
    (hL : ∀ X, ph = .reg X → ∀ i : Nat, S'.L[i]? = some (v3rpc.WatchReqM.cancel X) →
      S.L[i]? = some (v3rpc.WatchReqM.cancel X)) :
    noCancelOk (GF := GF) S P ph ⊢ noCancelOk S' P ph := by
  cases ph with
  | reg X =>
    unfold noCancelOk
    iintro (%H | #H)
    · ileft; ipureintro; intro i hi; exact H i (hL X rfl i hi)
    · iright; iexact H
  | _ => unfold noCancelOk; iintro -; itrivial

/-- The cancels of a list grown by one request that cancels no `X`. -/
theorem cancels_of_snoc {L L' : List v3rpc.WatchReqM} (x : v3rpc.WatchReqM) (X : w64)
    (hx : x ≠ v3rpc.WatchReqM.cancel X) (h : L' = L ∨ L' = L ++ [x]) :
    ∀ i : Nat, L'[i]? = some (v3rpc.WatchReqM.cancel X) → L[i]? = some (v3rpc.WatchReqM.cancel X) := by
  intro i hi
  rcases h with rfl | rfl
  · exact hi
  · rcases getElem?_snoc_cases hi with ⟨-, h⟩ | ⟨-, e⟩
    · exact h
    · exact absurd e.symm hx

/-- A list grown by a create request or not (`addCase`'s, `resume_ok`'s). -/
theorem create_or {L L' : List v3rpc.WatchReqM} (h : L' = L ∨ ∃ c, L' = L ++ [.create c]) (X : w64) :
    ∀ i : Nat, L'[i]? = some (v3rpc.WatchReqM.cancel X) → L[i]? = some (v3rpc.WatchReqM.cancel X) := by
  intro i hi
  rcases h with rfl | ⟨c, rfl⟩
  · exact hi
  · exact cancels_of_snoc (.create c) X (by intro e; cases e) (Or.inr rfl) i hi

/-- **A substream `run` made and has not seen stop**: its values, its phase (agreeing with the
maps, `phOk`), its id field, what `run` holds of it, and (unit W-K) its id never cancelled unless
it stopped (`noCancelOk`). -/
def wsElem (V : WEnv GF) (γs : StreamNames) (S : RunSt) (ws : Loc) : IProp GF :=
  iprop(∃ (P : WsPrm GF) (ph : WPh), ⌜P.ws = ws ∧ phOk S ws ph⌝ ∗ wsIs V P ∗
    wsF ws go!"id" ↦ ph.id ∗ wsRest V γs S.Dm P ph ∗ noCancelOk S P ph)

/-- **`run`'s state at a `return`** (the deferred teardown's precondition; the local `closeErr` at
`cep`, the `closing` map at `clm`): the close error, the maps, the substreams, the wait group's
adder, `run`'s thread token, `donec` not yet closed. -/
def runExit (V : WEnv GF) (G : WgsPrm GF) (cep clm : Loc) : IProp GF :=
  iprop(∃ (γs : StreamNames) (S : RunSt) (U : GMap Loc Unit) (ce e : GoInterface) (mref : Loc)
      (s : GoSlice),
    cep ↦ ce ∗ statusErrOk ce ∗ ownMap clm (DFrac.own 1) S.CL ∗
    wgsF G.wgs go!"substreams" ↦ mref ∗ ownMap mref (DFrac.own 1) S.M ∗
    wgsF G.wgs go!"resuming" ↦ s ∗ sliceOwn s S.l ∗
    wgsF G.wgs go!"closeErr" ↦ e ∗ statusErrOk e ∗ ⌜gOk S U⌝ ∗
    ghostMapAuth G.γws 1 U ∗ ([∗map] ws ↦ _u ∈ U, wsElem V γs S ws) ∗
    wgAdder G.wgs ∗ threadTok ∗ ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Pending)

/-- **`run`'s state at the head of its loop** (but its local variables): the maps, the gRPC
stream's sender token and `respc`'s consumer side, what it knows (`S`, `gOk`), the server's tokens
it holds, the substreams it made (`U`), the wait group's adder, its thread token, `donec`. -/
def runCore (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (γr : SpscNames) (clm csm : Loc) :
    IProp GF :=
  iprop(∃ (S : RunSt) (U : GMap Loc Unit) (rcv : List Loc) (mref : Loc) (s : GoSlice)
      (e : GoInterface),
    ownMap clm (DFrac.own 1) S.CL ∗ ownMap csm (DFrac.own 1) S.CS ∗
    wgsF G.wgs go!"substreams" ↦ mref ∗ ownMap mref (DFrac.own 1) S.M ∗
    wgsF G.wgs go!"resuming" ↦ s ∗ sliceOwn s S.l ∗
    wgsF G.wgs go!"closeErr" ↦ e ∗ statusErrOk e ∗
    cliSendTok (Req := v3rpc.pbWatchRequest) γs S.L ∗ spscConsumer γr rcv ∗
    ⌜rcv.length = S.Dm.length⌝ ∗ v3rpc.downLbW γs S.Dm ∗ ⌜gOk S U⌝ ∗
    ([∗list] i ∈ S.ansd, ansH γs i) ∗ ([∗list] X ∈ S.regs, idH γs X) ∗
    (□ [∗list] m ∈ S.Dm, respInfo m) ∗
    ghostMapAuth G.γws 1 U ∗ ([∗map] ws ↦ _u ∈ U, wsElem V γs S ws) ∗
    wgAdder G.wgs ∗ threadTok ∗ ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Pending)

theorem runExit_of_core (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (γr : SpscNames)
    (clm csm cep : Loc) (ce : GoInterface) :
    runCore V G γs γr clm csm ∗ cep ↦ ce ∗ statusErrOk ce ⊢ runExit V G cep clm := by
  iintro ⟨Hc, Hcep, #Hce⟩
  unfold runCore
  icases Hc with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, -, Hsub, Hm, Hres, Hs, HcF, #He, -, -, -,
    -, %HgOk, -, -, -, Hwsa, Hels, Had, Htt, Hdn⟩
  unfold runExit
  iexists γs, S, U, ce, e, mref, s
  iframe
  iframe #
  ipureintro; exact HgOk

theorem wsElem_mono (V : WEnv GF) (γs : StreamNames) {S S' : RunSt} (ws : Loc)
    (hD : S'.Dm = S.Dm) (h : ∀ ph, phOk S ws ph → phOk S' ws ph)
    (hL : ∀ X, phOk S ws (.reg X) → ∀ i : Nat, S'.L[i]? = some (v3rpc.WatchReqM.cancel X) →
      S.L[i]? = some (v3rpc.WatchReqM.cancel X)) :
    wsElem V γs S ws ⊢ wsElem V γs S' ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
  iexists P, ph
  rw [hD]
  iframe HP Hid Hrest
  isplitr
  · ipureintro; exact ⟨HPws, h ph Hph⟩
  iapply noCancelOk_mono P ph (fun X e => by subst e; exact hL X Hph) $$ Hnc

/-- **A cancel request `run` builds** (`&pb.WatchRequest{RequestUnion:
&pb.WatchRequest_CancelRequest{CancelRequest: &pb.WatchCancelRequest{WatchId: X}}}`), persisted. -/
theorem cancelReq_send (a b c : Loc) (X : w64)
    (s1 s3 : google_golang_org.protobuf.internal.impl.MessageState) (u1 u3 : GoSlice) (z1 z3 : w32) :
    a ↦ ({ state' := s1, WatchId' := X, unknownFields' := u1, sizeCache' := z1 } :
        etcdserverpb.WatchCancelRequest) ∗
      b ↦ ({ CancelRequest' := a } : etcdserverpb.WatchRequest_CancelRequest) ∗
      c ↦ ({ state' := s3,
             RequestUnion' :=
               interface.mkOk (go.GoType.PointerType etcdserverpb.WatchRequest_CancelRequest.ty) #b,
             unknownFields' := u3, sizeCache' := z3 } : etcdserverpb.WatchRequest) ⊢
    |==> v3rpc.watchReqSend (GF := GF) c (.cancel X) := by
  iintro ⟨Ha, Hb, Hc⟩
  ihave %Hann := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  iStructNamed Hb
  iStructNamed Hc
  ipersist WatchId; ipersist CancelRequest; ipersist RequestUnion
  imodintro
  unfold v3rpc.watchReqSend v3rpc.oneofCancel
  iexists _
  iframe RequestUnion
  iexists a
  isplitr
  · ipureintro; exact Hann
  isplitl []
  · iexists b
    isplitr
    · ipureintro; rfl
    iexact CancelRequest
  iexact WatchId

/-- A points-to, split in halves. -/
theorem ptsto_split_half (l : Loc) (v : w64) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
        typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) := by
  have h := ((fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional
    (1 : Qp).half (1 : Qp).half)
  rw [Qp.half_add_half] at h
  exact h.1

/-- A fresh substream (its id field owned) is none of those `run` made. -/
theorem wsElems_fresh (V : WEnv GF) (γs : StreamNames) (S : RunSt) (U : GMap Loc Unit) (ws : Loc)
    (v : w64) :
    ([∗map] w ↦ _u ∈ U, wsElem V γs S w) ∗ wsF ws go!"id" ↦ v ⊢
      ⌜U !! ws = none⌝ ∗ ([∗map] w ↦ _u ∈ U, wsElem V γs S w) ∗ wsF ws go!"id" ↦ v := by
  iintro ⟨Hm, Hid⟩
  cases h : U !! ws with
  | none => iframe; ipureintro; rfl
  | some u =>
    icases (BigSepM.bigSepM_lookup_acc h).1 $$ Hm with ⟨Hw, -⟩
    unfold wsElem
    icases Hw with ⟨%P, %ph, ⟨%HP, -⟩, -, Hid2, -⟩
    subst HP
    iexfalso
    iapply w64_ptsto_excl $$ [$Hid $Hid2]

theorem prefix_snoc_eq {α : Type} {D L : List α} {m : α}
    (h : D <+: L ++ [m] ∨ L ++ [m] <+: D) (hl : L.length = D.length) : L = D := by
  rcases h with h | h
  · rw [List.prefix_iff_eq_take] at h
    rw [h, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  · have := h.length_le; simp at this; omega

theorem evsSoFar_snoc_ctrl (Dm : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM) (w : Loc)
    (h : m.src = none) : evsSoFar (Dm ++ [m]) w = evsSoFar Dm w := by
  unfold evsSoFar
  rw [sentEvsOf_snoc, h]; simp

theorem wsRest_snoc_ctrl (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (P : WsPrm GF) (ph : WPh) (h : m.src = none) :
    wsRest V γs Dm P ph ⊢ wsRest V γs (Dm ++ [m]) P ph := by
  cases ph with
  | reg X =>
    simp only [wsRest]
    iintro ⟨%w, %rg, %fcs, %lo, %sent, %C, #Hrf, Hprod, Hauth, Hst, Hc2⟩
    ihave #Hrf' := regFacts_mono V γs P X w rg fcs lo (List.prefix_append Dm [m]) $$ Hrf
    iexists w, rg, fcs, lo, sent, C
    iframe Hrf' Hprod Hauth
    isplitl [Hst]
    · unfold cursorOk
      rw [evsSoFar_snoc_ctrl Dm m w h]
      iexact Hst
    iapply cur2St_mono V γs P X w rg lo sent (evsSoFar_snoc_ctrl Dm m w h)
      (List.prefix_append Dm [m]) $$ Hc2
  | queued si => simp only [wsRest]; iintro H; iexact H
  | closedRun X => simp only [wsRest]; iintro H; iexact H
  | orphan => simp only [wsRest]; iintro H; iexact H

theorem wsElem_mono' (V : WEnv GF) (γs : StreamNames) {S S' : RunSt} (ws : Loc)
    (hD : ∀ P ph, phOk S ws ph → wsRest V γs S.Dm P ph ⊢ wsRest V γs S'.Dm P ph)
    (h : ∀ ph, phOk S ws ph → phOk S' ws ph) (hLe : S'.L = S.L) :
    wsElem V γs S ws ⊢ wsElem V γs S' ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
  iexists P, ph
  ihave Hrest := hD P ph Hph $$ Hrest
  iframe HP Hid Hrest
  isplitr
  · ipureintro; exact ⟨HPws, h ph Hph⟩
  iapply noCancelOk_mono P ph (fun X _ i hi => by rw [hLe] at hi; exact hi) $$ Hnc

theorem sendTok_lookup (γs : StreamNames) (L : List v3rpc.WatchReqM) (i : Nat) (r : v3rpc.WatchReqM) :
    cliSendTok (GF := GF) (Req := v3rpc.pbWatchRequest) γs L ∗ v3rpc.upAtW γs i r ⊢
      cliSendTok (Req := v3rpc.pbWatchRequest) γs L ∗ ⌜L[i]? = some r⌝ := by
  iintro ⟨Ht, #Hu⟩
  unfold cliSendTok v3rpc.upAtW
  ihave %H := mono_list_auth_idx_lookup _ _ _ _ _ $$ Ht Hu
  iframe
  ipureintro; exact H

theorem ans_fresh (γs : StreamNames) (ansd : List Nat) (i : Nat) (γo : mvcc.WsStreamNames)
    (γa : GName) :
    ([∗list] j ∈ ansd, ansH (GF := GF) γs j) ∗ streamAuxIs γs (v3rpc.auxOf γo γa) ∗
      v3rpc.ansTok γa i ⊢
      ⌜i ∉ ansd⌝ ∗ ([∗list] j ∈ ansd, ansH γs j) ∗ v3rpc.ansTok γa i := by
  iintro ⟨Hl, #Hax, Ht⟩
  by_cases hi : i ∈ ansd
  · icases BigSepL.bigSepL_mem_acc hi $$ Hl with ⟨H, -⟩
    unfold ansH
    icases H with ⟨%γo', %γa', #Hax', Ht'⟩
    ihave %He : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo' γa'⌝) $$ []
    · iapply streamAuxIs_agree
      isplit
      · iexact Hax
      · iexact Hax'
    obtain ⟨-, rfl⟩ := v3rpc.auxOf_inj He
    iexfalso
    iapply v3rpc.ansTok_excl $$ [$Ht $Ht']
  · iframe; ipureintro; exact hi

theorem id_fresh (γs : StreamNames) (regs : List w64) (X : w64) (γo : mvcc.WsStreamNames)
    (γa : GName) :
    ([∗list] Y ∈ regs, idH (GF := GF) γs Y) ∗ streamAuxIs γs (v3rpc.auxOf γo γa) ∗
      mvcc.idTok γo X ⊢
      ⌜X ∉ regs⌝ ∗ ([∗list] Y ∈ regs, idH γs Y) ∗ mvcc.idTok γo X := by
  iintro ⟨Hl, #Hax, Ht⟩
  by_cases hi : X ∈ regs
  · icases BigSepL.bigSepL_mem_acc hi $$ Hl with ⟨H, -⟩
    unfold idH
    icases H with ⟨%γo', %γa', #Hax', Ht'⟩
    ihave %He : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo' γa'⌝) $$ []
    · iapply streamAuxIs_agree
      isplit
      · iexact Hax
      · iexact Hax'
    obtain ⟨rfl, -⟩ := v3rpc.auxOf_inj He
    iexfalso
    iapply mvcc.idTok_excl $$ [$Ht $Ht']
  · iframe; ipureintro; exact hi

/-- An event response of another watcher leaves a registered substream's cursor alone. -/
theorem wsRest_snoc_other (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (P : WsPrm GF) (X : w64) (hsrc : m.src = some ρ)
    (hX : ρ.id ≠ X) :
    mvcc.respOk ρ ∗ wsRest V γs Dm P (.reg X) ⊢ wsRest V γs (Dm ++ [m]) P (.reg X) := by
  iintro ⟨#Hr, H⟩
  simp only [wsRest]
  icases H with ⟨%w, %rg, %fcs, %lo, %sent, %C, #Hrf, Hprod, Hauth, Hrest, Hc2⟩
  ihave %Hne : ⌜ρ.w ≠ w ∨ ρ.evs = []⌝ $$ []
  · unfold mvcc.respOk
    icases Hr with ⟨-, %rr, %fcs', #Hf, %Hid⟩
    unfold regFacts mvcc.watcherIs
    icases Hrf with ⟨%Hcr, ⟨%γw, %C', -, #Hf', -⟩, -⟩
    by_cases hw : ρ.w = w
    · subst hw
      ihave %Hag : iprop(⌜rr = rg ∧ fcs' = fcs⌝) $$ []
      · iapply mvcc.watcherFixed_agree
        isplit
        · iexact Hf
        · iexact Hf'
      obtain ⟨rfl, -⟩ := Hag
      ipureintro
      right
      refine Classical.byContradiction fun hn => hX ?_
      rw [Hid.1 hn]; exact Hcr.2.2.1
    · ipureintro; left; exact hw
  have hev : evsSoFar (Dm ++ [m]) w = evsSoFar Dm w := by
    unfold evsSoFar
    rw [sentEvsOf_snoc, hsrc]
    rcases Hne with h | h
    · simp [h]
    · simp [h]
  ihave #Hrf' := regFacts_mono V γs P X w rg fcs lo (List.prefix_append Dm [m]) $$ Hrf
  iexists w, rg, fcs, lo, sent, C
  iframe Hrf' Hprod Hauth
  isplitl [Hrest]
  · unfold cursorOk
    rw [hev]
    iexact Hrest
  iapply cur2St_mono V γs P X w rg lo sent hev (List.prefix_append Dm [m]) $$ Hc2

/-- **A substream another response's id does not name** keeps its element across the response. -/
theorem wsElem_recv_other (V : WEnv GF) (γs : StreamNames) {S S' : RunSt} (ws : Loc)
    (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (hsrc : m.src = some ρ) (hD : S'.Dm = S.Dm ++ [m])
    (hX : ∀ X, phOk S ws (.reg X) → ρ.id ≠ X) (h : ∀ ph, phOk S ws ph → phOk S' ws ph)
    (hLe : S'.L = S.L) :
    mvcc.respOk ρ ∗ wsElem V γs S ws ⊢ wsElem V γs S' ws := by
  iintro ⟨#Hr, Hw⟩
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
  iexists P, ph
  rw [hD]
  iframe HP Hid
  isplitr
  · ipureintro; exact ⟨HPws, h ph Hph⟩
  isplitl [Hrest]
  · cases ph with
    | reg X =>
      iapply wsRest_snoc_other V γs S.Dm m ρ P X hsrc (hX X Hph)
      iframe Hrest; iexact Hr
    | queued si => iunfold wsRest at Hrest; simp only [wsRest]; iexact Hrest
    | closedRun X => simp only [wsRest]; itrivial
    | orphan => simp only [wsRest]; itrivial
  iapply noCancelOk_mono P ph (fun X _ i hi => by rw [hLe] at hi; exact hi) $$ Hnc

/-- **The `k`-th response to a substream** (`k ≠ 0`, not its creation's): an mvcc response's
`WatchResponse` at `wr`, its events `es` between the cursors `hiB` and `hiA`. -/
theorem recvElem_of (V : WEnv GF) (P : WsPrm GF) (k : Nat) (hk : k ≠ 0) (m : v3rpc.WatchRespM)
    (h : Loc) (sl : GoSlice) (es : List EvModel) (hiB hiA : w64) (wr : Loc)
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false) (hhn : h ≠ null)
    :
    wr ↦□ wrOf m h sl ∗ eventsAt sl es ∗
      watchHdrOwn h ⟨es, W64 0, false, false, m.hdr.revision⟩ ∗
      monoListIdxOwn P.γhi k hiB ∗ monoListIdxOwn P.γhi (k + 1) hiA ∗
      rangeWatchRespOk (EM := V.EM) V.pfx P.o P.rev hiB hiA ⟨es, W64 0, false, false, m.hdr.revision⟩ ∗
      recvCmpl V P k (wrOf m h sl) ⟨es, W64 0, false, false, m.hdr.revision⟩ ⊢
    recvElem V P k wr := by
  iintro ⟨#Hwr, #Hes, Hwo, #Hi0, #Hi1, #Hrok, #Hcm⟩
  unfold recvElem
  ileft
  iexists wrOf m h sl, ⟨es, W64 0, false, false, m.hdr.revision⟩, hiB, hiA
  simp only [wrOf, Int.toNat_natCast, Int.natCast_eq_zero, hk, ↓reduceIte]
  iframe Hwr Hes Hwo Hi0 Hi1 Hrok
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3⟩ := hfl
    simp [hhn, h1, h2, h3]
  isplitr
  · iexact Hcm
  ipureintro; first | trivial | rfl | simp [hfl.2.2]

/-- **What a promised completeness says of a watch** (pure; K2e-7d): its start revision was read,
non-zero, and its registered range covers exactly the keys under its key. -/
theorem cpl_facts (V : WEnv GF) (P : WsPrm GF) (X : w64) (rg : mvcc.WatchRange)
    (hok : wsReqOk V.pfx P) (hc : P.γ.cpl = cplOf P) (hcpl : P.γ.cpl = true)
    (hcr : v3rpc.createRangeOk (createOfP P) X rg) :
    P.sr = true ∧ 1 ≤ sint.Z P.rev ∧ (∀ k, rg.covers k = true ↔ P.o.key <+: k) ∧
      rg.startRev = P.rev ∧ rg.id = X := by
  rw [hc] at hcpl
  unfold cplOf cplCond at hcpl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcpl
  obtain ⟨hsr, hk, he, hff, hr0⟩ := hcpl
  obtain ⟨-, -, h0, -, hkey, hed, -, -⟩ := hok
  refine ⟨hsr, ?_, ?_, hcr.2.1, hcr.2.2.1⟩
  · have : sint.Z P.rev ≠ 0 := fun h => hr0 (by word)
    omega
  · have := covers_prefix (createOfP P) X rg hcr (by show P.key ≠ []; rw [hkey]; exact hk)
      (by show P.ed = prefixRangeEnd P.key; rw [hkey, hed]; exact he)
      (by show prefixRangeEnd P.key ≠ [W8 0]; rw [hkey]; exact hff)
    intro k; rw [this k]; show P.key <+: k ↔ _; rw [hkey]

/-- **A promised watch's first revision is its start revision.** -/
theorem cpl_lo (V : WEnv GF) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
    (rev : w64) (hst : rg.startRev = rev) (hr : 1 ≤ sint.Z rev) :
    mvcc.watcherIs (GF := GF) V.R.γ w rg fcs lo ⊢ ⌜lo = (sint.Z rev).toNat⌝ := by
  iintro #Hw
  iunfold mvcc.watcherIs at Hw
  icases Hw with ⟨%γw0, %C0, -, -, -, -, %Hlo⟩
  ipureintro
  rw [Hlo.2, hst, if_neg (fun h => by rw [h] at hr; simp at hr)]

/-- **The second cursor over an event-less mvcc response** `x` (the `j`th sent down, the
substream's own id `X` or `-1`, covering its watcher `w`): the cache's contract from the cursor
and the cursor after it (`cmpl_cov`, `cmpl_mono`, `cmpl_prog`). -/
theorem prog_cmpl (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (j : Nat) (m : v3rpc.WatchRespM) (x : mvcc.RespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange)
    (fcs : GoSlice) (lo : Nat) (c2 : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (r : RespModel) (hj : Dm.length = j) (hsrc : m.src = some x) (hxe : x.evs = [])
    (hlive : v3rpc.idLive Dm X) (hX1 : X ≠ W64 (-1)) (hxid : x.id = X ∨ x.id = W64 (-1))
    (hok : wsReqOk V.pfx P) (hcplP : P.γ.cpl = cplOf P) (hcpl : P.γ.cpl = true)
    (hst : V.R.γ.st = V.R.E.γ) (hv : ¬ watchErr v)
    (hr : r.events = [] ∧ r.created = false ∧ r.canceled = false ∧ r.compactRev = W64 0 ∧
      r.hdrRev = m.hdr.revision) (hwc : w ∈ x.cov) :
    cur2Ok V γs P Dm X w rg lo c2 ∗ v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs Dm ∗
      regFacts V γs Dm P X w rg fcs lo ∗ startOk V P.sr P.rev ∗ srvLogsSmall V.R ⊢
      ∃ c2' : w64, watchRespOk (EM := V.EM) P.o.key c2 c2' v r ∗
        cur2Ok V γs P (Dm ++ [m]) X w rg lo c2' := by
  iintro ⟨#Hc, #Hmv, #Hdn, #Hrf, #Hso, #Hsm⟩
  iunfold v3rpc.mvccOk at Hmv
  icases Hmv with ⟨%x', %rs, %L, %Hm, #HL, -, -, -, #Hcov, %Hfr⟩
  have hxx : x = x' := by
    have := congrArg v3rpc.WatchRespM.src Hm.1
    simp only [v3rpc.mvccResp] at this
    rw [hsrc] at this; exact Option.some.inj this
  subst hxx
  ihave %HLD : ⌜L = Dm⌝ $$ []
  · iunfold v3rpc.downLbW at HL Hdn
    ihave %Hcmp := mono_list_lb_valid _ L Dm $$ HL Hdn
    ipureintro
    have hl : L.length = Dm.length := by rw [hj]; exact Hm.2.2.1
    rcases Hcmp with h | h
    · exact h.eq_of_length hl
    · exact (h.eq_of_length hl.symm).symm
  subst HLD
  iunfold v3rpc.mvccCov at Hcov
  icases Hcov with ⟨%γc, %pre, %γo, %γa, #Hax, %Hγ, #Hfwd, #Hsl0, #Hrc, -, -⟩
  iunfold mvcc.respCov at Hrc
  icases Hrc with ⟨#Hcf, -, -, #Hrr⟩
  ihave #Hcfw := Hcf $$ %w %hwc
  iunfold regFacts at Hrf
  icases Hrf with ⟨%Hcr, #Hwi, #Hfcs, ⟨%γw, #Hmw, %Hsr⟩, -, -⟩
  obtain ⟨hsr, hrev1, hcov, hstart, hid⟩ := cpl_facts V P X rg hok hcplP hcpl Hcr
  ihave %Hlo := cpl_lo V w rg fcs lo P.rev hstart hrev1 $$ Hwi
  ihave #Hwi' := Hwi
  iunfold mvcc.watcherIs at Hwi'
  icases Hwi' with ⟨%γw0, %C0, -, #Hwfix, -, -, -⟩
  ihave %Hfe := Hfwd $$ %w %rg %fcs Hwfix
  have hfe := Hfe (by rw [hid]; exact hX1) (by rw [hid]; exact hlive) (by rw [hid]; exact hxid)
  ihave ⟨%Lc, %dd, %p, #HLc, %Hcc⟩ := cmpl_cov V L x γc pre w rg fcs lo hfe (by omega) $$ [Hcfw Hwi Hfcs Hmw]
  · iframe Hcfw Hwi Hfcs
    iexists γw; iframe Hmw; ipureintro; rw [Hsr, hsr]
  obtain ⟨hpx, hp63, hE, hd1, hd2, hd3, hlop⟩ := Hcc
  have hdd : dd = p + 1 := by omega
  subst hdd
  ihave %Hq := cmpl_mono V γs P L X w rg lo c2 x γc pre γo γa Lc p Hγ.2.2.1 Hγ.2.2.2 Hfr.2
    (hxid.symm.imp (fun h => h) (fun h => h)) hxe hE hlop Hlo hrev1 hpx hp63 $$ [Hc Hax Hsl0 Hrr]
  · iframe Hc Hax Hsl0 Hrr
  obtain ⟨q, hqc, hqp⟩ := Hq
  iunfold startOk at Hso
  icases Hso with ⟨-, (%hf | #Hr0)⟩
  · rw [hsr] at hf; cases hf
  ihave #Hpos : chanPos γs x $$ []
  · unfold chanPos
    iexists γc, pre, γo, γa
    iframe Hax Hsl0
    ipureintro; exact ⟨Hγ.2.2.1, Hγ.2.2.2⟩
  have hsnoc : evsOf (L ++ [m]) w = evsOf L w := by
    unfold evsOf
    rw [sentEvsOf_snoc, hsrc]
    simp [hxe]
  iapply cmpl_prog V γs P L m x X w rg lo c2 P.o.key hcov hst Lc (p + 1) p q hpx hp63 hqc hqp hE
    (Nat.le_refl _) (Or.inl (Nat.le_refl _)) hd3 hlop Hlo hrev1 hsnoc hsrc hxe hlive v r hv
    ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.trans Hm.2.1⟩
  iframe Hc HLc Hsm Hr0 Hpos

/-- **The second cursor, pending the dispatch's outcome** (K2e-7d): `γh2`'s positions, two more
than the responses dispatched before (the new one's), the last the cursor after the response. -/
def cur2Pend (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF)
    (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc) (C2 : List w64) :
    IProp GF :=
  iprop(monoListAuthOwn P.γh2 1 C2 ∗
    (⌜P.γ.cpl = false⌝ ∨ dghostVar P.γx DFrac.discard true ∨
      ⌜C2.length = sent.length + 2⌝ ∗ ∃ c2 : w64, ⌜C2.getLast? = some c2⌝ ∗
        cur2Ok V γs P Dm X w rg lo c2))

/-- **A dispatch's step of the second cursor** (K2e-7d): from a step of the cursor over the
response (`hstep`, with the persistent facts `Q`, when the watch promises completeness), the
cursor's pending state and the response's completeness part (`recvCmpl`), or the substream had
stopped. -/
theorem cmpl_step (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (P : WsPrm GF) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat)
    (sent : List Loc) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel)
    (Q : IProp GF) [Persistent Q]
    (hstep : P.γ.cpl = true → ∀ c2 : w64, cur2Ok V γs P Dm X w rg lo c2 ∗ Q ⊢
      ∃ c2' : w64, watchRespOk (EM := V.EM) P.o.key c2 c2' v r ∗
        cur2Ok V γs P (Dm ++ [m]) X w rg lo c2') :
    cur2St V γs Dm P X w rg lo sent ∗ Q ⊢
    |==> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P X w rg lo sent C2 ∗
      (dghostVar P.γx DFrac.discard true ∨ recvCmpl V P (sent.length : Int) v r) := by
  iintro ⟨Hc, #HQ⟩
  unfold cur2St
  icases Hc with ⟨%C2, Ha, (%Hf | #Hx | ⟨%Hl, %c2, %Hlc, #Hcur⟩)⟩
  · imodintro
    iexists C2
    unfold cur2Pend
    iframe Ha
    isplitr
    · ileft; ipureintro; exact Hf
    iright; unfold recvCmpl; ileft; ipureintro; exact Hf
  · imodintro
    iexists C2
    unfold cur2Pend
    iframe Ha
    isplitr
    · iright; ileft; iexact Hx
    ileft; iexact Hx
  cases hcpl : P.γ.cpl
  · imodintro
    iexists C2
    unfold cur2Pend
    iframe Ha
    isplitr
    · ileft; ipureintro; exact hcpl
    iright; unfold recvCmpl; ileft; ipureintro; exact hcpl
  ihave ⟨%c2', #Hok, #Hcur'⟩ := hstep hcpl c2 $$ [Hcur HQ]
  · iframe Hcur HQ
  imod monoListAuthOwn_update_app (γ := P.γh2) (l := C2) [c2'] $$ Ha with ⟨Ha, #Hlb⟩
  have h0 : (C2 ++ [c2'])[sent.length]? = some c2 := by
    rw [List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at Hlc
    rw [show sent.length = C2.length - 1 by omega]; exact Hlc
  have h1 : (C2 ++ [c2'])[sent.length + 1]? = some c2' := by
    rw [List.getElem?_append_right (by omega)]; simp [Hl]
  ihave #Hi0 := monoListIdxOwn_get (γ := P.γh2) sent.length c2 h0 $$ Hlb
  ihave #Hi1 := monoListIdxOwn_get (γ := P.γh2) (sent.length + 1) c2' h1 $$ Hlb
  imodintro
  iexists C2 ++ [c2']
  unfold cur2Pend
  iframe Ha
  isplitr
  · iright; iright
    isplitr
    · ipureintro; simp [Hl]
    iexists c2'
    iframe Hcur'
    ipureintro; simp
  iright
  unfold recvCmpl
  iright
  iexists c2, c2'
  simp only [Int.toNat_natCast]
  iframe Hi0 Hi1 Hok

/-- **An event-less response of a substream's own id covers its watcher** (K2e-7d): the id is
assigned to the response's watcher (`mvccExtra`), the substream's (`idAssigned`), and an event-less
response covers its watcher (`respCov`). -/
theorem own_cov (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (j : Nat) (m : v3rpc.WatchRespM)
    (x : mvcc.RespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
    (hsrc : m.src = some x) (hxe : x.evs = []) (hid : x.id = X) (hX1 : X ≠ W64 (-1)) :
    v3rpc.mvccOk γs V.R.γ j m ∗ regFacts V γs Dm P X w rg fcs lo ⊢ ⌜w ∈ x.cov⌝ := by
  iintro ⟨#Hmv, #Hrf⟩
  iunfold v3rpc.mvccOk at Hmv
  icases Hmv with ⟨%x', %rs, %L, %Hm, -, -, -, #Hx, #Hcov, -⟩
  have hxx : x = x' := by
    have := congrArg v3rpc.WatchRespM.src Hm.1
    simp only [v3rpc.mvccResp] at this
    rw [hsrc] at this; exact Option.some.inj this
  subst hxx
  iunfold v3rpc.mvccExtra at Hx
  icases Hx with ⟨#He, -⟩
  ihave ⟨%γo', %γa', #Hax', #Hia'⟩ := He $$ %(Or.inr (by rw [hid]; exact hX1))
  iunfold regFacts at Hrf
  icases Hrf with ⟨-, -, -, -, -, %γo, %γa, #Hax, #Hia⟩
  ihave %Heq : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo' γa'⌝) $$ []
  · iapply streamAuxIs_agree
    isplit
    · iexact Hax
    · iexact Hax'
  obtain ⟨rfl, -⟩ := v3rpc.auxOf_inj Heq
  irevert Hia'; rw [hid]; iintro #Hia'
  ihave %Hw := mvcc.idAssigned_agree γo X w x.w $$ [Hia Hia']
  · isplit
    · iexact Hia
    · iexact Hia'
  iunfold v3rpc.mvccCov at Hcov
  icases Hcov with ⟨%γc, %pre, %γo2, %γa2, -, -, -, -, #Hrc, -, -⟩
  iunfold mvcc.respCov at Hrc
  icases Hrc with ⟨-, -, %Hxw, -⟩
  ipureintro
  rw [Hw]; exact Hxw hxe

/-- **Before dispatching an mvcc response to its registered substream** (id `ρ.id`, watcher `w`,
`recvc` producer at `sent`, cursors `C`): the response's events, the header for `dispatchEvent`,
the content of the response for the substream (`recvElem`), the cursors extended by the new one
and the substream's state after it (the stop flag, or the cursor of the events received with this
response). -/
theorem reg_pre (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (j : Nat) (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (rs : List mvcc.RespM) (w : Loc)
    (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) (sent : List Loc) (C : List w64)
    (h : Loc) (sl : GoSlice) (ps : List Loc) (kvs : List Loc)
    (hsrc : m.src = some ρ) (hev : m.evs = ρ.evs)
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false)
    (hfilt : ρ.evs ≠ [] → v3rpc.sentEvsOf Dm ρ.w ++ [ρ] = rs.filter (fun x => decide (x.evs ≠ [])))
    (hps : ps.length = ρ.evs.length) (hkvl : kvs.length = ρ.evs.length)
    (hok : wsReqOk V.pfx P) (hpfx : V.pfx ≠ []) (hst : V.R.γ.st = V.R.E.γ) (hhn : h ≠ null)
    (hj : Dm.length = j) (hcplP : P.γ.cpl = cplOf P) (hlive : v3rpc.idLive Dm ρ.id)
    (hX1 : ρ.id ≠ W64 (-1)) :
    srvEventIdsAssigned V.R ∗ srvLogsSmall V.R ∗ srvNoDupKeys V.R ∗
      startOk V P.sr P.rev ∗ v3rpc.downLbW γs Dm ∗ cur2St V γs Dm P ρ.id w rg lo sent ∗
      v3rpc.mvccOk γs V.R.γ j m ∗ mvcc.watchRecvOk V.R.γ ρ.w rs ∗
      regFacts V γs Dm P ρ.id w rg fcs lo ∗ sl ↦*□ ps ∗
      ([∗list] x ∈ ps.zip ρ.evs, mvcc.evIs (GF := GF) x.1 x.2) ∗
      eventsAt sl (List.zipWith evModelOf ρ.evs kvs) ∗
      monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ ∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P Dm w rg lo hi) ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ m.hdr.revision ⊢
    |={⊤}=> ∃ (es : List EvModel) (C' C2 : List w64), eventsAt sl es ∗ ⌜es.length = m.evs.length⌝ ∗
      (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision) ∗ monoListAuthOwn P.γhi 1 C' ∗
      (∀ wr : Loc, wr ↦□ wrOf m h sl -∗ recvElem V P sent.length wr) ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ ∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P (Dm ++ [m]) w rg lo hi) ∗
      cur2Pend V γs (Dm ++ [m]) P ρ.id w rg lo sent C2 := by
  iintro ⟨#HS3, #Hsm, #Hnd, #Hso, #Hdn, Hc2, #Hmv, #Hrecv, #Hrf, #Hsl, #Hevs, #Hea, Hauth, Hst, Hrev⟩
  ihave #Hrf0 := Hrf
  ihave Hhdr : iprop(|==> ((⌜m.evs = []⌝ ∗ hdrAt h m.hdr.revision) ∨
      (⌜m.evs ≠ []⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ m.hdr.revision)))
      $$ [Hrev]
  · by_cases hne : m.evs = []
    · ipersist Hrev
      imodintro
      ileft
      isplitr
      · ipureintro; exact hne
      unfold hdrAt; iright
      iframe Hrev
      ipureintro; exact hhn
    · imodintro
      iright
      iframe
      ipureintro; exact hne
  imod Hhdr
  icases Hst with (#Hx | ⟨⟨%Hlen, %Hsne⟩, %hi, %Hlast, #Hcur⟩)
  · -- the substream stopped: nothing to give
    unfold cur2St
    icases Hc2 with ⟨%C2, Ha2, -⟩
    imodintro
    iexists List.zipWith evModelOf ρ.evs kvs, C, C2
    iframe Hea Hauth
    isplitr
    · ipureintro; simp [hkvl, hev]
    isplitl [Hhdr]
    · icases Hhdr with (⟨%hne, #Hha⟩ | ⟨%hne, -⟩)
      · iintro %-; iexact Hha
      · iintro %h'; exact absurd h' hne
    isplitr
    · iintro %wr -
      unfold recvElem
      iright; iexact Hx
    isplitr
    · ileft; iexact Hx
    unfold cur2Pend; iframe Ha2; iright; ileft; iexact Hx
  -- the substream runs: the response's content
  iunfold regFacts at Hrf
  icases Hrf with ⟨%Hcr, #Hwi, #Hfcs, -, -, %γo, %γa, #Hax, #Hias⟩
  ihave %hρw : ⌜ρ.evs ≠ [] → ρ.w = w⌝ $$ []
  · by_cases hne : ρ.evs = []
    · ipureintro; intro h'; exact absurd hne h'
    · iunfold srvEventIdsAssigned at HS3
      ihave ⟨%γo', %γa', #Hax', #Hias'⟩ := HS3 $$ %γs %j %m %ρ Hmv %(And.intro hsrc hne)
      ihave %He : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo' γa'⌝) $$ []
      · iapply streamAuxIs_agree
        isplit
        · iexact Hax
        · iexact Hax'
      obtain ⟨rfl, -⟩ := v3rpc.auxOf_inj He
      ihave %Hw := mvcc.idAssigned_agree γo ρ.id w ρ.w $$ [Hias Hias']
      · isplit
        · iexact Hias
        · iexact Hias'
      ipureintro; intro _; exact Hw.symm
  iunfold cursorOk at Hcur
  icases Hcur with ⟨%Hhi, #Hcut⟩
  have hfilt' : ρ.evs ≠ [] → v3rpc.sentEvsOf Dm w ++ [ρ] =
      rs.filter (fun x => decide (x.evs ≠ [])) := fun hne => by rw [← hρw hne]; exact hfilt hne
  ihave Hdc := dispatch_content V P Dm m
      ρ rs ρ.id w rg fcs lo hi sl ps m.hdr.revision hsrc hρw hfilt' hps hok hpfx hst Hcr Hhi $$ []
  · iframe #
  imod Hdc with ⟨%es, #Hes, %Hesl, #Hrok, %Hhi', #Hcut', %kvs', %Hkvs, #Hkv⟩
  -- (K2e-7d) the second cursor
  have hv : ¬ watchErr (wrOf m h sl) := by
    unfold watchErr wrOf; simp [hfl.1, hfl.2.1]
  ihave Hcmp : iprop(|==> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P ρ.id w rg lo sent C2 ∗
      (dghostVar P.γx DFrac.discard true ∨ recvCmpl V P (sent.length : Int) (wrOf m h sl)
        ⟨es, W64 0, false, false, m.hdr.revision⟩)) $$ [Hc2]
  · by_cases hne : ρ.evs = []
    · -- an event-less response of the substream's own id: a progress notification
      have hes0 : es = [] := by
        rw [← List.length_eq_zero_iff, Hesl, hne]; rfl
      ihave %Hwc := own_cov V γs P Dm j m ρ ρ.id w rg fcs lo hsrc hne rfl hX1 $$ [Hmv Hrf0]
      · iframe #
      iapply cmpl_step V γs Dm m P ρ.id w rg lo sent (wrOf m h sl) _
        iprop(v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs Dm ∗
          regFacts V γs Dm P ρ.id w rg fcs lo ∗ startOk V P.sr P.rev ∗ srvLogsSmall V.R)
        (fun hc c2 => by
          iintro ⟨#Hc, #Hq1, #Hq2, #Hq3, #Hq4, #Hq5⟩
          iapply prog_cmpl V γs P Dm j m ρ ρ.id w rg fcs lo c2 (wrOf m h sl) _ hj hsrc hne hlive
            hX1 (Or.inl rfl) hok hcplP hc hst hv ⟨hes0, rfl, rfl, rfl, rfl⟩ Hwc
          iframe #)
      iframe Hc2
      iframe #
    · -- events: the watcher's, the watch events of a watched log
      have hw := hρw hne
      ihave #Hrecv' : mvcc.watchRecvOk V.R.γ w rs $$ []
      · rw [← hw]; iexact Hrecv
      ihave ⟨%L2, %d, #HL2, %HL2d⟩ := recv_unfiltered V.R.γ w rs rg fcs lo $$ [Hrecv' Hwi Hfcs]
      · iframe #
      have h2 : evsOf Dm w ++ ρ.evs = mvcc.watchEvents L2 rg lo d := by
        rw [← evs_after Dm w rs ρ (hfilt' hne)]; exact HL2d.1
      have hsnoc : evsOf (Dm ++ [m]) w = evsOf Dm w ++ ρ.evs := by
        unfold evsOf
        rw [sentEvsOf_snoc, hsrc]
        simp [hw, hne]
      iapply cmpl_step V γs Dm m P ρ.id w rg lo sent (wrOf m h sl) _
        iprop(mvcc.evLog V.R.γ.st L2 ∗ srvLogsSmall V.R ∗
          □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜ρ.evs[k]? = some ev⌝ → ⌜kvs'[k]? = some kv⌝ →
            mvcc.kvPtrFixed kv ev.kv))
        (fun hc c2 => by
          iintro ⟨#Hc, #Hq1, #Hq2, #Hq3⟩
          obtain ⟨-, -, hcov, -, -⟩ := cpl_facts V P ρ.id rg hok hcplP hc Hcr
          iapply cmpl_events V γs P Dm m ρ.id w rg lo c2 P.o.key hcov hst L2 d ρ.evs kvs' Hkvs.2 hne
            hsnoc h2 HL2d.2 (wrOf m h sl) _ Hkvs.1 hv
          iframe #)
      iframe Hc2
      iframe #
  imod Hcmp with ⟨%C2, Hpend, #Hcm⟩
  imod monoListAuthOwn_update_app (γ := P.γhi) (l := C)
      [(es.getLast?.map EvModel.rev).getD hi] $$ Hauth with ⟨Hauth, #Hlb⟩
  have hC0 : (C ++ [(es.getLast?.map EvModel.rev).getD hi])[sent.length]? = some hi := by
    rw [List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at Hlast
    rw [show sent.length = C.length - 1 by omega]; exact Hlast
  have hC1 : (C ++ [(es.getLast?.map EvModel.rev).getD hi])[sent.length + 1]? =
      some ((es.getLast?.map EvModel.rev).getD hi) := by
    rw [List.getElem?_append_right (by omega)]
    simp [Hlen]
  ihave #Hi0 := monoListIdxOwn_get (γ := P.γhi) sent.length hi hC0 $$ Hlb
  ihave #Hi1 := monoListIdxOwn_get (γ := P.γhi) (sent.length + 1) ((es.getLast?.map EvModel.rev).getD hi) hC1 $$ Hlb
  ihave ⟨Hwo, Hhw⟩ : iprop(watchHdrOwn h ⟨es, W64 0, false, false, m.hdr.revision⟩ ∗
      (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision)) $$ [Hhdr]
  · icases Hhdr with (⟨%hne, #Hha⟩ | ⟨%hne, Hrev⟩)
    · have hes : es = [] := by
        rw [← List.length_eq_zero_iff, Hesl, ← hev, hne]; rfl
      simp only [watchHdrOwn, hes, ↓reduceIte]
      isplitl []
      · iexact Hha
      · iintro %-; iexact Hha
    · have hes : es ≠ [] := by
        intro e; apply hne; rw [← List.length_eq_zero_iff, hev, ← Hesl, e]; rfl
      simp only [watchHdrOwn, hes, ↓reduceIte]
      isplitl [Hrev]
      · iframe; ipureintro; exact hhn
      · iintro %h'; exact absurd h' hne
  imodintro
  iexists es, C ++ [(es.getLast?.map EvModel.rev).getD hi], C2
  iframe Hes Hhw Hauth Hpend
  isplitr
  · ipureintro; rw [Hesl, hev]
  isplitl [Hwo]
  · iintro %wr #Hwr
    icases Hcm with (#Hx2 | #Hcm')
    · unfold recvElem; iright; iexact Hx2
    iapply recvElem_of V P sent.length (by intro h0; exact Hsne (List.length_eq_zero_iff.1 h0)) m h
      sl es hi ((es.getLast?.map EvModel.rev).getD hi) wr hfl hhn
    iframe Hwr Hes Hwo Hi0 Hi1 Hrok Hcm'
  iright
  isplitr
  · ipureintro; simp [Hlen]
  iexists ((es.getLast?.map EvModel.rev).getD hi)
  isplitr
  · ipureintro; simp
  unfold cursorOk
  iframe Hcut'
  ipureintro; exact Hhi'

/-- **After dispatching to a registered substream**: its state over the new response, whether
the send succeeded or failed. -/
theorem reg_post (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
    (sent : List Loc) (C' C2 : List w64) (b : Bool) (wr : Loc) :
    regFacts V γs Dm P X w rg fcs lo ∗ monoListAuthOwn P.γhi 1 C' ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ ∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P (Dm ++ [m]) w rg lo hi) ∗
      cur2Pend V γs (Dm ++ [m]) P X w rg lo sent C2 ∗
      ((⌜b = true⌝ ∗ sendDone P sent wr) ∨ (⌜b = false⌝ ∗ sendFail V P sent wr)) ⊢
    wsRest V γs (Dm ++ [m]) P (.reg X) := by
  iintro ⟨#Hrf, Hauth, Hst, Hpend, Hs⟩
  simp only [wsRest]
  unfold cur2Pend
  icases Hpend with ⟨Ha2, Hp2⟩
  ihave #Hrf' := regFacts_mono V γs P X w rg fcs lo (List.prefix_append Dm [m]) $$ Hrf
  icases Hs with (⟨%-, Hd⟩ | ⟨%-, Hf⟩)
  · iunfold sendDone at Hd
    iexists w, rg, fcs, lo, sent ++ [wr], C'
    iframe Hrf' Hd Hauth
    isplitl [Hst]
    · icases Hst with (#Hx | ⟨%Hlen, %hi, %Hl, #Hc⟩)
      · ileft; iexact Hx
      · iright
        isplitr
        · ipureintro; simp [Hlen]
        iexists hi
        iframe Hc
        ipureintro; exact Hl
    unfold cur2St
    iexists C2
    iframe Ha2
    icases Hp2 with (%H | #H | ⟨%H, %c2, %Hl2, #Hc2⟩)
    · ileft; ipureintro; exact H
    · iright; ileft; iexact H
    · iright; iright
      isplitr
      · ipureintro; simp [H]
      iexists c2
      iframe Hc2
      ipureintro; exact Hl2
  · iunfold sendFail at Hf
    icases Hf with ⟨Hp, -, #Hx⟩
    iexists w, rg, fcs, lo, sent, C'
    iframe Hrf' Hp Hauth
    isplitr
    · ileft; iexact Hx
    unfold cur2St
    iexists C2
    iframe Ha2
    iright; ileft; iexact Hx

/-- **Before broadcasting a progress response to a registered substream** (unit W-K): the
response (no events) for the substream (`recvElem`, the cursor as it was), the cursors extended
by the same one, and the substream's state after it. -/
theorem bcast_pre (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (j : Nat) (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange)
    (fcs : GoSlice) (lo : Nat) (sent : List Loc) (C : List w64)
    (h : Loc) (sl : GoSlice) (hsrc : m.src = some ρ) (hev : ρ.evs = [])
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false) (hhn : h ≠ null)
    (hj : Dm.length = j) (hok : wsReqOk V.pfx P) (hcplP : P.γ.cpl = cplOf P)
    (hlive : v3rpc.idLive Dm X) (hX1 : X ≠ W64 (-1)) (hid : ρ.id = W64 (-1))
    (hst : V.R.γ.st = V.R.E.γ) :
    hdrAt h m.hdr.revision ∗ eventsAt sl [] ∗ monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ ∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P Dm w rg lo hi) ∗
      cur2St V γs Dm P X w rg lo sent ∗ (⌜w ∈ ρ.cov⌝ ∨ dghostVar P.γx DFrac.discard true) ∗
      v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs Dm ∗ regFacts V γs Dm P X w rg fcs lo ∗
      startOk V P.sr P.rev ∗ srvLogsSmall V.R ⊢
    |==> ∃ C' C2 : List w64, monoListAuthOwn P.γhi 1 C' ∗
      (∀ wr : Loc, wr ↦□ wrOf m h sl -∗ recvElem V P sent.length wr) ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ ∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P (Dm ++ [m]) w rg lo hi) ∗
      cur2Pend V γs (Dm ++ [m]) P X w rg lo sent C2 := by
  iintro ⟨#Hha, #Hea, Hauth, Hst, Hc2, #Hmem, #Hmv, #Hdn, #Hrf, #Hso, #Hsm⟩
  icases Hst with (#Hx | ⟨⟨%Hlen, %Hsne⟩, %hi, %Hlast, #Hcur⟩)
  · unfold cur2St
    icases Hc2 with ⟨%C2, Ha2, -⟩
    imodintro
    iexists C, C2
    iframe Hauth
    isplitr
    · iintro %wr -
      unfold recvElem
      iright; iexact Hx
    isplitr
    · ileft; iexact Hx
    unfold cur2Pend; iframe Ha2; iright; ileft; iexact Hx
  have hv : ¬ watchErr (wrOf m h sl) := by
    unfold watchErr wrOf; simp [hfl.1, hfl.2.1]
  ihave Hcmp : iprop(|==> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P X w rg lo sent C2 ∗
      (dghostVar P.γx DFrac.discard true ∨ recvCmpl V P (sent.length : Int) (wrOf m h sl)
        ⟨[], W64 0, false, false, m.hdr.revision⟩)) $$ [Hc2]
  · icases Hmem with (%Hwc | #Hx2)
    · iapply cmpl_step V γs Dm m P X w rg lo sent (wrOf m h sl) _
        iprop(v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs Dm ∗
          regFacts V γs Dm P X w rg fcs lo ∗ startOk V P.sr P.rev ∗ srvLogsSmall V.R)
        (fun hc c2 => by
          iintro ⟨#Hc, #Hq1, #Hq2, #Hq3, #Hq4, #Hq5⟩
          iapply prog_cmpl V γs P Dm j m ρ X w rg fcs lo c2 (wrOf m h sl) _ hj hsrc hev hlive
            hX1 (Or.inr hid) hok hcplP hc hst hv ⟨rfl, rfl, rfl, rfl, rfl⟩ Hwc
          iframe #)
      iframe Hc2
      iframe #
    · unfold cur2St
      icases Hc2 with ⟨%C2, Ha2, -⟩
      imodintro
      iexists C2
      unfold cur2Pend
      iframe Ha2
      isplitr
      · iright; ileft; iexact Hx2
      ileft; iexact Hx2
  imod Hcmp with ⟨%C2, Hpend, #Hcm⟩
  imod monoListAuthOwn_update_app (γ := P.γhi) (l := C) [hi] $$ Hauth with ⟨Hauth, #Hlb⟩
  have hC0 : (C ++ [hi])[sent.length]? = some hi := by
    rw [List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at Hlast
    rw [show sent.length = C.length - 1 by omega]; exact Hlast
  have hC1 : (C ++ [hi])[sent.length + 1]? = some hi := by
    rw [List.getElem?_append_right (by omega)]
    simp [Hlen]
  ihave #Hi0 := monoListIdxOwn_get (γ := P.γhi) sent.length hi hC0 $$ Hlb
  ihave #Hi1 := monoListIdxOwn_get (γ := P.γhi) (sent.length + 1) hi hC1 $$ Hlb
  have hevs : evsSoFar (Dm ++ [m]) w = evsSoFar Dm w := by
    unfold evsSoFar
    rw [sentEvsOf_snoc, hsrc]
    simp [hev]
  imodintro
  iexists C ++ [hi], C2
  iframe Hauth Hpend
  isplitr
  · iintro %wr #Hwr
    icases Hcm with (#Hx2 | #Hcm')
    · unfold recvElem; iright; iexact Hx2
    iapply recvElem_of V P sent.length (by intro h0; exact Hsne (List.length_eq_zero_iff.1 h0)) m h
      sl [] hi hi wr hfl hhn
    iframe Hwr Hea Hi0 Hi1 Hcm'
    isplitr
    · simp only [watchHdrOwn, ↓reduceIte]; iexact Hha
    unfold rangeWatchRespOk
    isplitr
    · ipureintro; simp [EvRevSorted]
    iintro !> %i %e %he
    simp at he
  iright
  isplitr
  · ipureintro; simp [Hlen]
  iexists hi
  isplitr
  · ipureintro; simp
  unfold cursorOk
  rw [hevs]
  iexact Hcur

/-- **A broadcast covers a registered substream's watcher, unless it stopped** (persistent;
K2e-7d): for the substream `ws` at the id `X`, whatever its values. -/
def bcastCov (V : WEnv GF) (γs : StreamNames) (S : RunSt) (ρ : mvcc.RespM) (X : w64) (ws : Loc) :
    IProp GF :=
  iprop(□ ∀ (P : WsPrm GF) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat),
    ⌜P.ws = ws⌝ -∗ regFacts V γs S.Dm P X w rg fcs lo -∗ noCancelOk S P (.reg X) -∗
      (⌜w ∈ ρ.cov⌝ ∨ dghostVar P.γx DFrac.discard true))

instance bcastCov_persistent (V : WEnv GF) (γs : StreamNames) (S : RunSt) (ρ : mvcc.RespM)
    (X : w64) (ws : Loc) : Persistent (bcastCov V γs S ρ X ws) := by
  unfold bcastCov; infer_instance

instance cancelQ_timeless (γs : StreamNames) (id : w64) : Timeless (v3rpc.cancelQ (GF := GF) γs id) := by
  unfold v3rpc.cancelQ v3rpc.upAtW; infer_instance

/-- **(a) A registered substream's watcher was registered on the channel before a broadcast**
(K2e-7d): at an index at most the broadcast's position `pre`'s length; the broadcast `x`, sent after
the substream's created response (not among the responses received, `hfresh`), is not in the
created response's snapshot, whose `-1` responses were all sent before it. -/
theorem bcast_regPair (V : WEnv GF) (γs : StreamNames) {S : RunSt} (X : w64) (ws : Loc)
    (x : mvcc.RespM) (γc : mvcc.WatchChanNames) (pre : List mvcc.RespM) (γo : mvcc.WsStreamNames)
    (γa : GName) (hM : S.M !! X = some ws)
    (hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y)
    (hregi : γo.regi = γc.regi) (hsentl : γo.sentl = γc.sentl)
    (hfresh : ∀ m' ∈ S.Dm, m'.src ≠ some x) (hid : x.id = W64 (-1)) :
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ mvcc.chanSentLb γc (pre ++ [x]) ∗ wsElem V γs S ws ⊢
      wsElem V γs S ws ∗ □ (∃ (w : Loc) (n : Nat), mvcc.idAssigned γo X w ∗ mvcc.chanRegAt γc w n ∗
        ⌜n ≤ pre.length⌝) := by
  iintro ⟨#Hax, #Hlb, Hw⟩
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
  have hph0 : ph = WPh.reg X := by
    cases ph with
    | queued si => exact absurd hM (Hph.1 X)
    | orphan => exact absurd hM (Hph.1 X)
    | closedRun Y => exact absurd hM (Hph.1.2.1 X)
    | reg Y => rw [hinj Y X ws Hph.1 hM]
  subst hph0
  iunfold wsRest at Hrest
  icases Hrest with ⟨%w, %rg, %fcs, %lo, %sent, %C, #Hrg, Hprod, Hauth, Hst, Hc2⟩
  ihave #Hrg' := Hrg
  iunfold regFacts at Hrg'
  icases Hrg' with ⟨-, -, -, -, #Hsnap, %γo1, %γa1, #Hax1, #Hia⟩
  iunfold regSnap at Hsnap
  icases Hsnap with ⟨%γo2, %γa2, %l, %L, %n, #Hax2, #Hl, #Hrn, %Hs⟩
  ihave %He1 : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo1 γa1⌝) $$ []
  · iapply streamAuxIs_agree; isplit
    · iexact Hax
    · iexact Hax1
  ihave %He2 : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo2 γa2⌝) $$ []
  · iapply streamAuxIs_agree; isplit
    · iexact Hax
    · iexact Hax2
  obtain ⟨rfl, rfl⟩ := v3rpc.auxOf_inj He1
  obtain ⟨rfl, rfl⟩ := v3rpc.auxOf_inj He2
  have hxl : x ∉ l := by
    intro hx
    obtain ⟨m', hm', hs⟩ := Hs.2.2 x hx hid
    exact hfresh m' (Hs.2.1.subset hm') hs
  iunfold mvcc.streamSentLb at Hl
  iunfold mvcc.chanSentLb at Hlb
  irevert Hl; rw [hsentl]; iintro #Hl
  ihave %Hcmp := mono_list_lb_valid γc.sentl l (pre ++ [x]) $$ Hl Hlb
  have hll : l.length ≤ pre.length := by
    rcases Hcmp with h | h
    · obtain ⟨t, ht⟩ := h
      cases t with
      | nil => rw [List.append_nil] at ht; exact absurd (ht ▸ List.mem_append_right _ (List.mem_singleton_self x)) hxl
      | cons a t =>
        have := congrArg List.length ht
        simp at this; omega
    · exact absurd (h.subset (List.mem_append_right _ (List.mem_singleton_self x))) hxl
  isplitl [Hid Hprod Hauth Hst Hc2]
  · iexists P, .reg X
    iframe HP Hid Hnc
    isplitr
    · ipureintro; exact ⟨HPws, Hph⟩
    simp only [wsRest]
    iexists w, rg, fcs, lo, sent, C
    iframe Hrg Hprod Hauth Hst Hc2
  iintro !>
  iexists w, n
  iframe Hia
  isplitr
  · iapply (mvcc.chanRegAt_stream γo γc w n hregi).2; iexact Hrn
  ipureintro; omega

/-- Picking the watchers of a list of ids (persistent facts with existentials). -/
theorem regs_collect (Q : w64 → Loc → Nat → IProp GF) [∀ X w n, Persistent (Q X w n)] :
    ∀ kvs : List (w64 × Loc), □ ([∗list] kv ∈ kvs, ∃ w n, Q kv.1 w n) ⊢
      ∃ ps : List (w64 × Loc × Nat), ⌜ps.map Prod.fst = kvs.map Prod.fst⌝ ∗
        □ ([∗list] p ∈ ps, Q p.1 p.2.1 p.2.2)
  | [] => by iintro -; iexists []; isplitr
             · ipureintro; rfl
             iintro !>; iapply BigSepL.bigSepL_nil.2; itrivial
  | kv :: kvs => by
    iintro #H
    ihave ⟨⟨%w, %n, #Hq⟩, #Ht⟩ := BigSepL.bigSepL_cons.1 $$ H
    ihave ⟨%ps, %Hps, #Hps⟩ := regs_collect Q kvs $$ Ht
    iexists (kv.1, w, n) :: ps
    isplitr
    · ipureintro; simp [Hps]
    iintro !>
    iapply BigSepL.bigSepL_cons.2
    iframe Hq Hps

/-- **(b) A broadcast lists every registered substream's watcher** (K2e-7d; `regsAt`, one
credit): for the ids of `M`, their watchers registered at indices at most `k`. -/
theorem bcast_regs (γc : mvcc.WatchChanNames) (k : Nat) (x : mvcc.RespM) (M : GMap w64 Loc)
    (γo : mvcc.WsStreamNames) (hid : x.id = W64 (-1)) :
    mvcc.regsAt (GF := GF) γc k x ∗ £ 1 ∗
      □ ([∗map] X ↦ _ws ∈ M, ∃ (w : Loc) (n : Nat), mvcc.idAssigned γo X w ∗ mvcc.chanRegAt γc w n ∗
        ⌜n ≤ k⌝) ⊢
      |={⊤}=> □ (∀ (X : w64) (ws w : Loc), ⌜M !! X = some ws⌝ -∗ mvcc.idAssigned γo X w -∗
        ⌜w ∈ x.regs⌝) := by
  iintro ⟨#Hra, Hlc, #Hm⟩
  ihave #Hl := (BigSepM.bigSepM_toList (Φ := fun X (_ : Loc) => iprop(∃ (w : Loc) (n : Nat),
    mvcc.idAssigned (GF := GF) γo X w ∗ mvcc.chanRegAt γc w n ∗ ⌜n ≤ k⌝)) (m := M)).1 $$ Hm
  ihave ⟨%ps, %Hps, #Hpl⟩ := regs_collect (fun X w n => iprop(mvcc.idAssigned (GF := GF) γo X w ∗
    mvcc.chanRegAt γc w n ∗ ⌜n ≤ k⌝)) (Iris.Std.toList M) $$ Hl
  ihave #Hreg : □ ([∗list] p ∈ ps.map (fun (p : w64 × Loc × Nat) => (p.2.1, p.2.2)), mvcc.chanRegAt γc p.1 p.2) $$ []
  · iintro !>
    rw [BigSepL.bigSepL_map]
    iapply (BigSepL.bigSepL_mono (Φ := fun _ (p : w64 × Loc × Nat) => iprop(mvcc.idAssigned (GF := GF)
      γo p.1 p.2.1 ∗ mvcc.chanRegAt γc p.2.1 p.2.2 ∗ ⌜p.2.2 ≤ k⌝))
      (fun {_ _} _ => by iintro ⟨-, #H, -⟩; iexact H)) $$ Hpl
  ihave %Hle : ⌜∀ p ∈ ps.map (fun (p : w64 × Loc × Nat) => (p.2.1, p.2.2)), p.2 ≤ k⌝ $$ []
  · ihave Hp := BigSepL.bigSepL_mono (Φ := fun _ (p : w64 × Loc × Nat) => iprop(mvcc.idAssigned
      (GF := GF) γo p.1 p.2.1 ∗ mvcc.chanRegAt γc p.2.1 p.2.2 ∗ ⌜p.2.2 ≤ k⌝))
      (Ψ := fun _ (p : w64 × Loc × Nat) => iprop(⌜p.2.2 ≤ k⌝))
      (fun {_ _} _ => by iintro ⟨-, -, %H⟩; ipureintro; exact H) $$ Hpl
    ihave %Hp' := BigSepL.bigSepL_pure_intro $$ Hp
    ipureintro
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
    exact Hp' i q hi
  iunfold mvcc.regsAt at Hra
  imod Hra $$ %(ps.map (fun (p : w64 × Loc × Nat) => (p.2.1, p.2.2))) Hreg %Hle %hid Hlc with %Hin
  imodintro
  iintro !> %X %ws %w %hX #Hia
  have hmem : (X, ws) ∈ Iris.Std.toList M := Iris.Std.toList_get.2 hX
  have hX' : X ∈ ps.map Prod.fst := by rw [Hps]; exact List.mem_map.2 ⟨(X, ws), hmem, rfl⟩
  obtain ⟨q, hq, hqX⟩ := List.mem_map.1 hX'
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
  ihave ⟨#Hiq, -, -⟩ := (BigSepL.bigSepL_lookup (Φ := fun _ (p : w64 × Loc × Nat) =>
    iprop(mvcc.idAssigned (GF := GF) γo p.1 p.2.1 ∗ mvcc.chanRegAt γc p.2.1 p.2.2 ∗ ⌜p.2.2 ≤ k⌝)) hi)
    $$ Hpl
  irevert Hiq; rw [hqX]; iintro #Hiq
  ihave %Hw := mvcc.idAssigned_agree γo X w q.2.1 $$ [Hia Hiq]
  · isplit
    · iexact Hia
    · iexact Hiq
  ipureintro
  rw [Hw]
  exact Hin (q.2.1, q.2.2) (List.mem_map.2 ⟨q, hq, rfl⟩)

/-- **(c) A registered watcher a broadcast does not cover was cancelled at the client's request**
(K2e-7d): `respCompl`'s cancellation reason is the client's cancel request (`cancelQ`, saved at the
channel's reason), which the client sent (`cliSendTok`). -/
theorem cov_cancel (γs : StreamNames) (γc : mvcc.WatchChanNames) (L : List v3rpc.WatchReqM)
    (x : mvcc.RespM) :
    ∀ ws : List Loc, cliSendTok (GF := GF) (Req := v3rpc.pbWatchRequest) γs L ∗
      (□ ∀ w : Loc, ⌜w ∈ ws⌝ -∗ ⌜w ∈ x.cov⌝ ∨ mvcc.rsnW γc w) ∗
      savedPredOwn γc.rsn DFrac.discard (v3rpc.cancelQ γs) ⊢
      ◇ (cliSendTok (Req := v3rpc.pbWatchRequest) γs L ∗
        □ (∀ w : Loc, ⌜w ∈ ws⌝ -∗ ⌜w ∈ x.cov⌝ ∨ ∃ (rr : mvcc.WatchRange) (fcs : GoSlice) (i : Nat),
          mvcc.watcherFixed w rr fcs ∗ ⌜L[i]? = some (.cancel rr.id)⌝))
  | [] => by
    iintro ⟨Ht, -, -⟩
    imodintro
    iframe Ht
    iintro !> %w %hw; cases hw
  | w0 :: ws => by
    iintro ⟨Ht, #H, #Hcq⟩
    imod cov_cancel γs γc L x ws $$ [Ht] with ⟨Ht, #Hih⟩
    · iframe Ht Hcq
      iintro !> %w %hw
      iapply H $$ %w %(List.mem_cons_of_mem _ hw)
    icases H $$ %w0 %(List.mem_cons_self) with (%Hc | #Hr)
    · imodintro
      iframe Ht
      iintro !> %w %hw
      rcases List.mem_cons.1 hw with rfl | hw
      · ileft; ipureintro; exact Hc
      · iapply Hih $$ %w %hw
    iunfold mvcc.rsnW at Hr
    icases Hr with ⟨%rr, %fcs, #Hf, #Hrsn⟩
    iunfold mvcc.rsnFor at Hrsn
    icases Hrsn with ⟨%Ψ, #Hsp, #HΨ⟩
    ihave Heq := saved_pred_agree γc.rsn _ _ Ψ (v3rpc.cancelQ γs) rr.id $$ Hsp Hcq
    ihave Hl : ▷ v3rpc.cancelQ γs rr.id $$ [Heq]
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨H1, -⟩
      iapply H1
      iexact HΨ
    imod Hl with #Hq
    iunfold v3rpc.cancelQ at Hq
    icases Hq with ⟨%i, #Hu⟩
    icases sendTok_lookup γs L i (.cancel rr.id) $$ [Ht Hu] with ⟨Ht, %HLi⟩
    · iframe Ht Hu
    imodintro
    iframe Ht
    iintro !> %w %hw
    rcases List.mem_cons.1 hw with rfl | hw
    · iright; iexists rr, fcs, i; iframe Hf; ipureintro; exact HLi
    · iapply Hih $$ %w %hw

/-- **A broadcast covers every registered substream's watcher, unless it stopped** (K2e-7d):
(a), (b), (c) above, for the substreams of `substreams` (`S.M`), with one later credit. -/
theorem bcast_covAll (V : WEnv GF) (γs : StreamNames) {S : RunSt} (x : mvcc.RespM)
    (γc : mvcc.WatchChanNames) (pre : List mvcc.RespM) (γo : mvcc.WsStreamNames) (γa : GName)
    (hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y)
    (hregi : γo.regi = γc.regi) (hrsn : γo.rsn = γc.rsn) (hsentl : γo.sentl = γc.sentl)
    (hfresh : ∀ m' ∈ S.Dm, m'.src ≠ some x) (hid : x.id = W64 (-1)) :
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ mvcc.chanSentLb γc (pre ++ [x]) ∗
      mvcc.regsAt γc pre.length x ∗ mvcc.respCompl γc x ∗
      savedPredOwn γo.rsn DFrac.discard (v3rpc.cancelQ γs) ∗ £ 1 ∗
      cliSendTok (Req := v3rpc.pbWatchRequest) γs S.L ∗ ([∗map] _X ↦ ws ∈ S.M, wsElem V γs S ws) ⊢
      |={⊤}=> cliSendTok (Req := v3rpc.pbWatchRequest) γs S.L ∗
        ([∗map] _X ↦ ws ∈ S.M, wsElem V γs S ws) ∗
        □ (∀ (X : w64) (ws : Loc), ⌜S.M !! X = some ws⌝ -∗ bcastCov V γs S x X ws) := by
  iintro ⟨#Hax, #Hlb, #Hra, #Hcmp, #Hcq, Hlc, Ht, Hm⟩
  ihave Hm2 := BigSepM.bigSepM_impl (Ψ := fun X ws => iprop(wsElem V γs S ws ∗
      □ (∃ (w : Loc) (n : Nat), mvcc.idAssigned γo X w ∗ mvcc.chanRegAt γc w n ∗ ⌜n ≤ pre.length⌝)))
      $$ Hm []
  · iintro !> %X %ws %hX Hw
    iapply bcast_regPair V γs X ws x γc pre γo γa hX hinj hregi hsentl hfresh hid
    iframe Hax Hlb Hw
  rw [BigSepM.bigSepM_sep_eq]
  icases Hm2 with ⟨Hm, #Hps⟩
  ihave #Hps' : □ ([∗map] X ↦ _ws ∈ S.M, ∃ (w : Loc) (n : Nat), mvcc.idAssigned γo X w ∗
      mvcc.chanRegAt γc w n ∗ ⌜n ≤ pre.length⌝) $$ []
  · iintro !>
    iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by iintro #H; iexact H)) $$ Hps
  imod bcast_regs γc pre.length x S.M γo hid $$ [Hlc] with #Hreg
  · iframe Hra Hlc Hps'
  iunfold mvcc.respCompl at Hcmp
  icases Hcmp with (%hne | ⟨#Hc, -⟩)
  · exact absurd hid hne
  irevert Hcq; rw [hrsn]; iintro #Hcq
  imod cov_cancel γs γc S.L x x.regs $$ [Ht] with ⟨Ht, #Hcc⟩
  · iframe Ht Hc Hcq
  imodintro
  iframe Ht Hm
  iintro !> %X %ws %hX
  unfold bcastCov
  iintro !> %P %w %rg %fcs %lo %HPws #Hrf #Hnc
  iunfold regFacts at Hrf
  icases Hrf with ⟨%Hcr, #Hwi, -, -, -, %γo1, %γa1, #Hax1, #Hia⟩
  ihave %He : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo1 γa1⌝) $$ []
  · iapply streamAuxIs_agree; isplit
    · iexact Hax
    · iexact Hax1
  obtain ⟨rfl, rfl⟩ := v3rpc.auxOf_inj He
  ihave %Hwr := Hreg $$ %X %ws %w %hX Hia
  icases Hcc $$ %w %Hwr with (%Hcv | ⟨%rr, %fcs', %i, #Hf, %HLi⟩)
  · ileft; ipureintro; exact Hcv
  iunfold mvcc.watcherIs at Hwi
  icases Hwi with ⟨%γw0, %C0, -, #Hf0, -⟩
  ihave %Hag := mvcc.watcherFixed_agree w rg rr fcs fcs' $$ [$Hf0 $Hf]
  obtain ⟨rfl, -⟩ := Hag
  rw [Hcr.2.2.1] at HLi
  unfold noCancelOk
  icases Hnc with (%Hn | #Hx)
  · exact absurd HLi (Hn i)
  iright; iexact Hx

/-- **A registered substream, for a broadcast** (unit W-K): its send capability for the progress
response (`sendCap`, its values and `recvc` history), and its element after the send, whether it
succeeded or failed; (K2e-7d) the second cursor over the response, with its coverage
(`bcastCov`) and what the server says of it. -/
theorem bcast_elem (V : WEnv GF) (γs : StreamNames) {S S' : RunSt} (X : w64) (ws : Loc)
    (j : Nat) (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (h : Loc) (sl : GoSlice)
    (hsrc : m.src = some ρ)
    (hev : ρ.evs = []) (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false)
    (hhn : h ≠ null) (hM : S.M !! X = some ws)
    (hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y)
    (hD : S'.Dm = S.Dm ++ [m]) (hph : ∀ ph, phOk S ws ph → phOk S' ws ph) (hLe : S'.L = S.L)
    (hj : S.Dm.length = j) (hid : ρ.id = W64 (-1)) (hst : V.R.γ.st = V.R.E.γ) :
    hdrAt h m.hdr.revision ∗ eventsAt sl [] ∗ bcastCov V γs S ρ X ws ∗
      v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs S.Dm ∗ srvLogsSmall V.R ∗
      wsElem V γs S ws ⊢
    |==> ∃ a : WsPrm GF × List Loc, ⌜a.1.ws = ws⌝ ∗
      sendCap V a.1 a.2 (fun wr => iprop(wr ↦□ wrOf m h sl)) ∗
      (∀ wr : Loc, (sendDone a.1 a.2 wr ∨ sendFail V a.1 a.2 wr) -∗ wsElem V γs S' ws) := by
  iintro ⟨#Hha, #Hea, #Hbc, #Hmv, #Hdn, #Hsm, Hw⟩
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
  have hph0 : ph = WPh.reg X := by
    cases ph with
    | queued si => exact absurd hM (Hph.1 X)
    | orphan => exact absurd hM (Hph.1 X)
    | closedRun Y => exact absurd hM (Hph.1.2.1 X)
    | reg Y => rw [hinj Y X ws Hph.1 hM]
  subst hph0
  iunfold wsRest at Hrest
  icases Hrest with ⟨%w, %rg, %fcs, %lo, %sent, %C, #Hrg, Hprod, Hauth, Hst, Hc2⟩
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨-, -, -, -, -, -, -, -, -, %HPpure, #Hso⟩
  iunfold bcastCov at Hbc
  ihave #Hmem := Hbc $$ %P %w %rg %fcs %lo %HPws Hrg Hnc
  imod bcast_pre V γs P S.Dm j m ρ X w rg fcs lo sent C h sl hsrc hev hfl hhn hj HPpure.2.1
      HPpure.2.2 Hph.2.2.2.2.2.2.2 Hph.2.2.2.2.1 hid hst
      $$ [$Hha $Hea $Hauth $Hst $Hc2 $Hmem $Hmv $Hdn $Hrg $Hso $Hsm]
    with ⟨%C', %C2, Hauth, Hrecv, Hst, Hpend⟩
  imodintro
  iexists (P, sent)
  isplitr
  · ipureintro; exact HPws
  isplitl [Hprod Hrecv]
  · unfold sendCap
    iframe HP Hprod
    iintro %wr Hwr
    iapply Hrecv $$ Hwr
  iintro %wr Hs
  iexists P, .reg X
  isplitr
  · ipureintro; exact ⟨HPws, hph _ Hph⟩
  iframe HP Hid
  rw [hD]
  isplitl [Hs Hauth Hst Hpend]
  · icases Hs with (Hd | Hf)
    · iapply reg_post V γs P S.Dm m X w rg fcs lo sent C' C2 true wr
      iframe Hrg Hauth Hst Hpend
      ileft; iframe Hd; ipureintro; rfl
    · iapply reg_post V γs P S.Dm m X w rg fcs lo sent C' C2 false wr
      iframe Hrg Hauth Hst Hpend
      iright; iframe Hf; ipureintro; rfl
  iapply noCancelOk_mono P (.reg X) (fun X _ i hi => by rw [hLe] at hi; exact hi) $$ Hnc

/-- A failed dispatch publishes the substream's stop (`sendFail`'s `γx`), kept. -/
theorem post_gx (V : WEnv GF) (P : WsPrm GF) (sent : List Loc) (wr : Loc) (b : Bool) :
    ((⌜b = true⌝ ∗ sendDone P sent wr) ∨ (⌜b = false⌝ ∗ sendFail V P sent wr)) ⊢
      ((⌜b = true⌝ ∗ sendDone P sent wr) ∨ (⌜b = false⌝ ∗ sendFail V P sent wr)) ∗
        (⌜b = true⌝ ∨ dghostVar P.γx DFrac.discard true) := by
  iintro (⟨%hb, Hd⟩ | ⟨%hb, Hf⟩)
  · isplitl
    · ileft; iframe Hd; ipureintro; exact hb
    ileft; ipureintro; exact hb
  · iunfold sendFail at Hf
    icases Hf with ⟨Hp, Hr, #Hx⟩
    isplitl
    · iright; isplitr
      · ipureintro; exact hb
      iunfold sendFail; iframe Hp Hr Hx
    iright; iexact Hx

/-- **An id in `substreams`** is registered and not `-1` (its substream's phase says so). -/
theorem M_entry_facts (V : WEnv GF) (γs : StreamNames) {S : RunSt} {U : GMap Loc Unit} {X : w64}
    {ws : Loc} (hg : gOk S U) (hM : S.M !! X = some ws) :
    ([∗map] ws' ↦ _u ∈ U, wsElem V γs S ws') ⊢
      ⌜X ∈ S.regs ∧ X ≠ W64 (-1)⌝ ∗ ([∗map] ws' ↦ _u ∈ U, wsElem V γs S ws') := by
  iintro Hels
  have hU : U !! ws = some () := hg.1 X ws hM
  icases (BigSepM.bigSepM_delete hU).1 $$ Hels with ⟨Hw, Hels⟩
  iunfold wsElem at Hw
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
  have Hf : X ∈ S.regs ∧ X ≠ W64 (-1) := by
    cases ph with
    | queued si => exact absurd hM (Hph.1 X)
    | orphan => exact absurd hM (Hph.1 X)
    | reg Y =>
      have := hg.2.1 X Y ws hM Hph.1; subst this; exact ⟨Hph.2.2.2.1, Hph.2.2.2.2.1⟩
    | closedRun Y => exact absurd hM (Hph.1.2.1 X)
  isplitr
  · ipureintro; exact Hf
  iapply (BigSepM.bigSepM_delete hU).2
  iframe Hels
  unfold wsElem
  iexists P, ph
  iframe HP Hid Hrest Hnc
  ipureintro; exact ⟨HPws, Hph⟩

/-- **A new watcher's events so far are none**: an mvcc response with events of the watcher `w`
(range `rg`, of the id `X`) received before would name the id `X`, registered by then. -/
theorem evsSoFar_fresh {S : RunSt} {U : GMap Loc Unit} (X : w64) (w : Loc) (rg : mvcc.WatchRange)
    (fcs : GoSlice) (hg : gOk S U) (hX : X ∉ S.regs) (hX1 : X ≠ W64 (-1)) (hrg : rg.id = X) :
    (□ [∗list] m ∈ S.Dm, respInfo (GF := GF) m) ∗ mvcc.watcherFixed w rg fcs ⊢
      ⌜evsSoFar S.Dm w = []⌝ := by
  iintro ⟨#Hinfo, #Hf⟩
  by_cases hc : v3rpc.sentEvsOf S.Dm w = []
  · ipureintro; unfold evsSoFar; rw [hc]; rfl
  iexfalso
  obtain ⟨ρ, hρ⟩ := List.exists_mem_of_ne_nil _ hc
  unfold v3rpc.sentEvsOf at hρ
  simp only [List.mem_filter, decide_eq_true_eq] at hρ
  obtain ⟨hρm, hρw, hρe⟩ := hρ
  obtain ⟨m', hm', hsrc'⟩ := List.mem_filterMap.1 hρm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm'
  icases BigSepL.bigSepL_mem_acc hm' $$ Hinfo with ⟨#Hi, -⟩
  irevert Hi
  unfold respInfo
  rw [hsrc']
  iintro #Hr
  iunfold mvcc.respOk at Hr
  icases Hr with ⟨-, %rr, %fcs', #Hf', %Hid⟩
  subst hρw
  ihave %Hag : iprop(⌜rg = rr ∧ fcs = fcs'⌝) $$ []
  · iapply mvcc.watcherFixed_agree
    isplit
    · iexact Hf
    · iexact Hf'
  obtain ⟨rfl, -⟩ := Hag
  have hid := Hid.1 hρe
  have hl := hg.2.2.2.2.2.2.2.2.2.2.2.1 j m' ρ hj hsrc' (by rw [hid, hrg]; exact hX1)
  obtain ⟨mc, hmc, hs, hw, hcr, hca⟩ := idLive_exists hl
  have := hg.2.2.2.2.2.2.2.2.2.2.2.2 mc (List.mem_of_mem_take hmc) hs hcr hca
  exfalso; apply hX; rw [← hrg, ← hid, ← hw]; exact this

/-- **The first response to a substream**, its creation's (no events, the cursor `hi` both
before and after, the request's `rev` field's half). -/
theorem recvElem_created (V : WEnv GF) (P : WsPrm GF) (m : v3rpc.WatchRespM) (h : Loc)
    (sl : GoSlice) (hi rv : w64) (wr : Loc)
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = true) (hhn : h ≠ null) :
    wr ↦□ wrOf m h sl ∗ eventsAt sl [] ∗ hdrAt h m.hdr.revision ∗
      monoListIdxOwn P.γhi 0 hi ∗ monoListIdxOwn P.γhi 1 hi ∗
      recvCmpl V P 0 (wrOf m h sl) ⟨[], W64 0, false, true, m.hdr.revision⟩ ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} rv ⊢
    recvElem V P 0 wr := by
  iintro ⟨#Hwr, #Hes, #Hha, #Hi0, #Hi1, #Hcm, Hrv⟩
  unfold recvElem
  ileft
  iexists wrOf m h sl, ⟨[], W64 0, false, true, m.hdr.revision⟩, hi, hi
  simp only [wrOf, Int.toNat_zero, Nat.zero_add, ↓reduceIte]
  iframe Hwr Hes Hi0 Hi1
  obtain ⟨h1, h2, h3⟩ := hfl
  isplitr
  · ipureintro; simp [hhn, h1, h2, h3]
  isplitr
  · unfold watchHdrOwn; simp only [↓reduceIte]; iexact Hha
  isplitr
  · unfold rangeWatchRespOk
    isplitr
    · ipureintro; simp [EvRevSorted]
    imodintro
    iintro %k %e %hk
    simp at hk
  isplitr
  · iexact Hcm
  isplitr
  · ipureintro; simp
  iexists rv; iexact Hrv

/-- The ids registered after a created response: a new one unless refused. -/
theorem regs_join (γs : StreamNames) (b : Bool) (regs : List w64) (X : w64) :
    ([∗list] Y ∈ regs, idH (GF := GF) γs Y) ∗ ([∗list] Y ∈ (if b then [] else [X]), idH γs Y) ⊢
      [∗list] Y ∈ (if b then regs else regs ++ [X]), idH γs Y := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H1, H2⟩
    iapply BigSepL.bigSepL_append.2
    iframe
  · simp only [↓reduceIte]
    iintro ⟨H1, -⟩
    iexact H1

/-- Some watch parameters (for a dispatch with no target). -/
def dummyWsPrm (G : WgsPrm GF) (γr : SpscNames) : WsPrm GF :=
  WsPrm.mk (OpFull.mk OpModel.zero (W64 0) [] false false false (W64 0) [] false (W64 0) (W64 0)
    false false) (W64 0) G.ctx G.cd [] [] false false false slice.nil null G.γreq null
    (EtcdWatchNames.mk γr G.γws G.γws false) null null γr G.γws G.γws null G.γreq G.γws false

/-- A substream's id field, any value (`closeSubstream`'s). -/
def idE (ws : Loc) : IProp GF := iprop(∃ id : w64, wsF ws go!"id" ↦ id)

/-- What the teardown closes of a substream in its phase: `recvc` (its producer) if `run` holds it. -/
def closerRes (V : WEnv GF) (ws : Loc) : WPh → IProp GF
  | .queued _ => recvcCloser V ws
  | .reg _ => recvcCloser V ws
  | _ => iprop(True)

/-- A substream's closer, with its phase. -/
def closerE (V : WEnv GF) (S : RunSt) (ws : Loc) : IProp GF :=
  iprop(∃ ph : WPh, ⌜phOk S ws ph⌝ ∗ closerRes V ws ph)

theorem wsElem_split (V : WEnv GF) (γs : StreamNames) (S : RunSt) (ws : Loc) :
    wsElem V γs S ws ⊢ idE ws ∗ closerE V S ws ∗ donecOf ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
  subst HPws
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨-, -, -, #Hdc, -, -, #Hdb, -⟩
  isplitl [Hid]
  · unfold idE; iexists _; iexact Hid
  isplitl [Hrest]
  · unfold closerE
    iexists ph
    isplitr
    · ipureintro; exact Hph
    cases ph with
    | queued si =>
      unfold wsRest closerRes recvcCloser
      icases Hrest with ⟨Hprod, -⟩
      iexists P, []
      iframe HP Hprod
      ipureintro; rfl
    | reg X =>
      unfold wsRest closerRes recvcCloser
      icases Hrest with ⟨%w, %rg, %fcs, %lo, %sent, %C, -, Hprod, -⟩
      iexists P, sent
      iframe HP Hprod
      ipureintro; rfl
    | closedRun X => unfold closerRes; itrivial
    | orphan => unfold closerRes; itrivial
  unfold donecOf
  iexists P.donec, P.γdn, _
  iframe Hdc Hdb

theorem wsElems_split (V : WEnv GF) (γs : StreamNames) (S : RunSt) (U : GMap Loc Unit) :
    ([∗map] ws ↦ _u ∈ U, wsElem V γs S ws) ⊢
      ([∗map] ws ↦ _u ∈ U, idE ws) ∗ ([∗map] ws ↦ _u ∈ U, closerE V S ws) ∗
      □ (∀ ws, ⌜U !! ws = some ()⌝ → donecOf ws) := by
  refine (BigSepM.bigSepM_mono_of_forall (fun {_ _} => wsElem_split V γs S _)).trans ?_
  rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]
  iintro ⟨Hid, Hcl, #Hdc⟩
  iframe Hid Hcl
  imodintro
  iintro %ws %Hws
  iapply (BigSepM.bigSepM_lookup (Φ := fun ws (_ : Unit) => donecOf (GF := GF) ws) Hws) $$ Hdc

/-- The teardown's closing loops' facts: the substreams still to close (`U1`), those of `U` the
closing map (`CL'`) does not hold, the original closing map within it. -/
def tdOk (S : RunSt) (U CL' U1 : GMap Loc Unit) : Prop :=
  (∀ ws, U1 !! ws = some () → U !! ws = some ()) ∧
  (∀ ws, U !! ws = some () → CL' !! ws = none → U1 !! ws = some ()) ∧
  (∀ ws, S.CL !! ws = some () → CL' !! ws = some ())

theorem tdOk_init (S : RunSt) (U : GMap Loc Unit) : tdOk S U S.CL U :=
  ⟨fun _ h => h, fun _ h _ => h, fun _ h => h⟩

theorem tdOk_close {S : RunSt} {U CL' U1 : GMap Loc Unit} (h : tdOk S U CL' U1) (ws : Loc) :
    tdOk S U (GMap.insert ws () CL') (GMap.delete ws U1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun w hw => ?_, fun w hw hc => ?_, fun w hw => ?_⟩
  · by_cases e : ws = w
    · subst e; rw [GMap.lookup_delete] at hw; cases hw
    · rw [GMap.lookup_delete_ne _ e] at hw; exact h1 w hw
  · by_cases e : ws = w
    · subst e; rw [GMap.lookup_insert] at hc; cases hc
    · rw [GMap.lookup_insert_ne _ _ e] at hc; rw [GMap.lookup_delete_ne _ e]; exact h2 w hw hc
  · by_cases e : ws = w
    · subst e; rw [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ e]; exact h3 w hw

end defs
end client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem watchGRPCStream.run.wp_proof
    (wp_newWC : watchGRPCStream.newWatchClient.spec (GF := GF) (hG := hG))
    (wp_nextResume : watchGRPCStream.nextResume.spec (GF := GF) (hG := hG))
    (wp_dispatch : watchGRPCStream.dispatchEvent.spec (GF := GF) (hG := hG))
    (wp_addSub : watchGRPCStream.addSubstream.spec (GF := GF) (hG := hG))
    (wp_closeSub : watchGRPCStream.closeSubstream.spec (GF := GF) (hG := hG))
    (wp_join : watchGRPCStream.joinSubstreams.spec (GF := GF) (hG := hG))
    (wp_serveSub : watchGRPCStream.serveSubstream.spec (GF := GF) (hG := hG))
    (wp_bufLogger : watchGRPCStream.newWatcherStreamBufLogger.spec (GF := GF) (hG := hG))
    (wp_toPB : watchRequest.toPB.spec (GF := GF) (hG := hG))
    (wp_ptoPB : progressRequest.toPB.spec (GF := GF) (hG := hG))
    (wp_closeStream : watcher.closeStream.spec (GF := GF) (hG := hG))
    (wp_isHaltErr : isHaltErr.spec (GF := GF) (hG := hG))
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (wp_zapError : zap.Error.spec (GF := GF) (hG := hG))
    (wp_zapInt64 : zap.Int64.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.run.spec (GF := GF) (hG := hG) := by
  intro V G callSl m0 s0 rc γrc γresp
  wp_start as ⟨#HW, #HG, #Hco, Hsub, Hm0, Hres, Hs0, HcE, Hrc, Hrcb, #Hrespc, Hrespo, Hdn, Had,
    Htt, Hwsa⟩
  ihave #HG' := HG
  iunfold isWGS at HG'
  icases HG' with ⟨%Hwgs, -, #Hsf, %Hlg, #Fowner, #Fremote, #FcallOpts, #Fctx, #FctxKey, #Fcancel,
    #Freqc, #Frespc, #Fdonec, #Ferrc, #Fclosingc, #Flg, #HGctx, #HGcancel, #Hreqb, #Herrb, #Hclb,
    #HGdone⟩
  ihave #Hsf' := Hsf
  iunfold watchSrvFacts at Hsf'
  icases Hsf' with ⟨#Hstub, #Hconn⟩
  iunfold watchConnFacts at Hconn
  icases Hconn with ⟨#Hgc, #Hgs, #Hdesc, #Htoks, #HnoRetry, #Hsmall, #HnoDup,
    #Heof, #HerrNew, #Hcea, #Hvars, %Hpre⟩
  -- S2 and S3, facts of the verified server (unit W-M2)
  ihave #HS2 := srvProgressAllAnswers_holds V.R
  ihave #HS3 := srvEventIdsAssigned_holds V.R
  wp_apply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply (wp_map_make1 (K := Loc) (V := Unit) (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcherStream.ty)
    (go.GoType.StructType [])) as %clm Hclm
  ipersist w
  ipersist closing
  wp_bind (exceptionDo _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = #()⌝ ∗ client.runExit V G closeErr_ptr clm)))
  isplitl [Hsub Hm0 Hres Hs0 HcE Hrc Hrcb Hrespo Hdn Had Htt Hwsa wc closeErr Hclm]
  · wp_apply wp_newWC V G callSl m0 s0 rc γrc γresp $$ [Hsub Hm0 Hres Hs0 Hrc Hrcb Hrespo]
      as %wcv %err ⟨%m1, %s1, %rc1, %γrc1, Hsub, Hm1, Hres, Hs1, Hrc, Hrcb, Hcase⟩
    · iframe #; iframe
    icases Hcase with (⟨%Herr, %γs, %Dn, %cd', %γr, #Hcws, Hstok, #Hspec, #Hrspsc, Hrcons⟩ |
      ⟨⟨%Hwcn, %Herr⟩, #Hse, -, Hrespo⟩)
    rotate_left
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei =>
      wp_auto
      isplitr
      · ipureintro; rfl
      unfold client.runExit
      iexists (StreamNames.mk G.γws G.γws G.γws G.γws G.γws G.γws G.γws), client.RunSt.init, ∅,
        GoInterface.ok ei, GoInterface.nil, m1, s1
      simp only [client.RunSt.init]
      iframe
      iframe Hse
      ihave #Hnil := statusErrOk_nil (GF := GF)
      iframe Hnil
      isplitr
      · ipureintro; exact client.gOk_init
      iapply BigSepM.bigSepM_empty.2
      itrivial
    subst Herr
    iunfold v3rpc.cliWatchStreamIs at Hcws
    iunfold cliBidiStreamIs at Hcws
    icases Hcws with ⟨%ci, %Hci, #HSend, #HRecv, -, -⟩
    subst Hci
    wp_auto
    wp_apply (wp_map_make1 (K := w64) (V := Unit) go.int64 (go.GoType.StructType [])) as %csm Hcsm
    simp only [_root_.Perennial.time.Millisecond]
    wp_auto
    ipersist wc
    ipersist cancelSet
    ipersist Hrc
    ihave #Hrcu := ownBroadcastChan_Unknown $$ Hrcb
    imod monoListLbOwn_nil (GF := GF) (A := v3rpc.WatchRespM) γs.down with #Hlb0
    ihave IH : iprop(∃ bo : w64, "Hcore" ∷ client.runCore V G γs γr clm csm ∗
        "closeErr" ∷ closeErr_ptr ↦ GoInterface.nil ∗ "cur" ∷ cur_ptr ↦ (null : Loc) ∗
        "backoff" ∷ backoff_ptr ↦ bo) $$ [Hclm Hcsm Hsub Hm1 Hres Hs1 HcE Hstok Hrcons Hwsa Had Htt Hdn
        closeErr cur backoff]
    · iexists _
      simp only [named]
      iframe
      unfold client.runCore
      iexists client.RunSt.init, ∅, [], m1, s1, GoInterface.nil
      simp only [client.RunSt.init]
      iframe
      ihave #Hnil := statusErrOk_nil (GF := GF)
      iframe Hnil
      isplitr
      · ipureintro; rfl
      isplitr
      · unfold v3rpc.downLbW; iexact Hlb0
      isplitr
      · ipureintro; exact client.gOk_init
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      isplitr
      · imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
      iapply BigSepM.bigSepM_empty.2
      itrivial
    ihave #HGc := HGctx
    iNamedPrefix HGc "W"
    wp_for IH
    wp_apply +noauto WHDone as %dch %dγ #Hdone
    wp_auto_lc 6
    wp_apply_core chan.wp_select_blocking
    -- reqc
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists go_etcd_io.etcd.client.v3.watchStreamRequest, inferInstance, inferInstance, inferInstance,
        inferInstance, G.reqc, G.γreq
      isplit
      · ipureintro; rfl
      isplit
      · iapply is_bag_is_chan $$ Hreqb
      iapply bag_recv_au G.γreq G.reqc (reqP V) _ $$ [$Hlc1 $Hlc2] Hreqb
      inext
      iintro %rv #Hrq
      iunfold reqP at Hrq
      icases Hrq with (⟨%wr, %P0, ⟨%Hrv, %Hwrn⟩, #Hro, #Hrrev, #Hrretc, #Hctx, #Hretb, %Hok, #Hsrd0⟩ |
        ⟨%pr, %Hrv⟩)
      rotate_left
      · -- a progress request (unit W-K): sent up the stream
        subst Hrv
        iunfold client.runCore at Hcore
        icases Hcore with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, Hcsm, Hsub, Hm, Hres, Hs, HcF, #He,
          Hstok, Hrcons, %Hrcv, #HDlb, %HgOk, Hans, Hids, #Hinfo, Hwsa, Hels, Had, Htt, Hdn⟩
        wp_auto
        wp_apply wp_ptoPB pr as %preq Hpsend
        wp_apply HSend $$ %S.L %preq %(.progress) [Hstok Hpsend] as %err ⟨-, Hres'⟩
        · iframe
          unfold v3rpc.watchUp v3rpc.watchReqOk
          isplitr <;> itrivial
        ihave ⟨%L', %HL', Hstok⟩ : iprop(∃ L' : List v3rpc.WatchReqM,
            ⌜L' = S.L ∨ L' = S.L ++ [.progress]⌝ ∗ cliSendTok (Req := v3rpc.pbWatchRequest) γs L')
            $$ [Hres']
        · icases Hres' with (⟨-, Htok⟩ | ⟨-, %L', %HL', Htok⟩)
          · iexists _; iframe; ipureintro; right; rfl
          · iexists L'; iframe; ipureintro; exact HL'
        obtain ⟨Hg2, Hph2⟩ := client.progress_ok (S := S) (U := U) HgOk HL'
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => client.wsElem V γs (S.sentProgress L') ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          iapply (client.wsElem_mono V γs (S := S) (S' := S.sentProgress L') ws' rfl
            (fun ph' h => Hph2 ws' ph' h)
            (fun X _ => client.cancels_of_snoc .progress X (by intro e; cases e) HL')) $$ Hw'
        ihave Hfin : iprop(▷ client.runCore V G γs γr clm csm) $$
            [Hclm Hcsm Hsub Hm Hres Hs HcF Hstok Hrcons Hans Hids Hwsa Hels Had Htt Hdn]
        · inext
          unfold client.runCore
          iexists S.sentProgress L', U, rcv, mref, s, e
          have r0 : (S.sentProgress L').Dm = S.Dm := rfl
          have r1 : (S.sentProgress L').ansd = S.ansd := rfl
          have r2 : (S.sentProgress L').regs = S.regs := rfl
          have r3 : (S.sentProgress L').M = S.M := rfl
          have r4 : (S.sentProgress L').CL = S.CL := rfl
          have r5 : (S.sentProgress L').l = S.l := rfl
          have r6 : (S.sentProgress L').L = L' := rfl
          have r7 : (S.sentProgress L').CS = S.CS := rfl
          rw [r0, r1, r2, r3, r4, r5, r6, r7]
          iframe
          iframe #
          ipureintro; exact ⟨Hrcv, Hg2⟩
        cases err with
        | nil =>
          wp_auto
          wp_for_post
          iframe Hrcb
          iexists bo
          simp only [named]
          iframe closeErr cur backoff
          iexact Hfin
        | ok ei =>
          wp_auto
          wp_apply wp_zapError as %f1 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          wp_auto
          wp_apply wp_Debug V.lg _ _ $$ []
          · iframe #; ipureintro; exact Hlg
          wp_for_post
          iframe Hrcb
          iexists bo
          simp only [named]
          iframe closeErr cur backoff
          iexact Hfin
      subst Hrv
      iunfold client.runCore at Hcore
      icases Hcore with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, Hcsm, Hsub, Hm, Hres, Hs, HcF, #He,
        Hstok, Hrcons, %Hrcv, #HDlb, %HgOk, Hans, Hids, #Hinfo, Hwsa, Hels, Had, Htt, Hdn⟩
      wp_auto
      wp_apply (chan.wp_make2 (V := go_etcd_io.etcd.client.v3.WatchResponse) (W64 1)) as
        %outc %γo ⟨#Houtc, %Hγo, Houto⟩
      · ipureintro; word
      ihave #Hwrv : iprop(wr ↦□ (go_etcd_io.etcd.client.v3.watchRequest.mk (interface.ok P0.ctx)
          P0.key P0.ed P0.rev P0.cn P0.pn false P0.wbl P0.flt false P0.retc)) $$ []
      · iunfold wrRO at Hro
        icases Hro with ⟨#Rctx, #Rkey, #Rend, #Rcn, #Rpn, #Rfrag, #Rwbl, #Rflt, -, #RprevKV⟩
        iapply typedPointsto_combine _ _ _ Hwrn
        simp only [TypedPointsto.typedPointstoDef]
        iframe #
      wp_auto
      wp_apply (chan.wp_make1 (V := Loc)) as %recvc %γrc2 ⟨#Hrecvc, %Hγrc2, Hrecvo⟩
      ihave %Hwsn := typedPointsto_not_null _ _ _ $$ «$r0»
      iStructNamed «$r0»
      iStructNamed initReq
      ipersist ctx; ipersist key; ipersist end'; ipersist createdNotify; ipersist progressNotify
      ipersist fragment; ipersist watchBufLogEnabled; ipersist filters; ipersist prevKV
      ipersist outc; ipersist recvc
      icases client.ptsto_split_half _ _ $$ rev with ⟨Hrev1, Hrev2⟩
      wp_bind (If _ _ _)
      iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ws_ptr ↦ «$r0_ptr» ∗ ∃ bl : Loc,
          wsF «$r0_ptr» go!"bufLogger" ↦ bl ∗ bufLogOk «$r0_ptr» bl)))
      isplitl [bufLogger ws]
      · cases hw : P0.wbl
        · wp_auto
          isplitr
          · ipureintro; rfl
          iframe
          unfold bufLogOk; ileft; ipureintro; rfl
        · wp_auto
          ihave #Hnf : (□ ∀ Φ : val → IProp GF, ▷ (∀ t : _root_.Perennial.time.Time, Φ #t) -∗
              WP (App (Val #(functions _root_.Perennial.time.Now [])) (Val #())) {{ Φ }}) $$ []
          · imodintro; iintro %Φ' HΦ'
            wp_apply time.wp_Now as %t1 -
            iapply HΦ'
          wp_apply wp_bufLogger G.wgs «$r0_ptr» V.lg P0.key P0.ed _ $$ [] as %bl #Hbl
          · iframe #; ipureintro; exact Hlg
          isplitr
          · ipureintro; rfl
          iframe
          unfold bufLogOk; iright; iexact Hbl
      iintro %v ⟨%Hv, ws, %bl, HbL, #HbLok⟩
      subst Hv
      wp_auto
      wp_apply (chan.wp_make1 (V := Unit)) as %dnc %γdn ⟨#Hdnc, %-, Hdno⟩
      ipersist donec
      imod dghostVar_alloc false with ⟨%γx, Hx⟩
      imod alloc_broadcast_chan (E := ⊤) (dghostVar γx DFrac.discard true) γdn dnc $$ Hdnc Hdno
        with Hdnb
      icases ownBroadcastChan_dup_unknown _ _ _ _ $$ Hdnb with ⟨Hdnb, #Hdnu⟩
      imod mono_list_own_alloc (GF := GF) [P0.rev - W64 1] with ⟨%γhi, Hhia, #Hhilb⟩
      imod mono_list_own_alloc (GF := GF) [P0.rev - W64 1] with ⟨%γcur, Hcura, #Hcurlb⟩
      ihave #Hhi0 := monoListIdxOwn_get (GF := GF) 0 (P0.rev - W64 1) rfl $$ Hhilb
      ihave #Hcur0 := monoListIdxOwn_get (GF := GF) 0 (P0.rev - W64 1) rfl $$ Hcurlb
      -- (K2e-7d) the second cursors: the dispatch's and the contract's
      imod mono_list_own_alloc (GF := GF) [P0.rev - W64 1] with ⟨%γh2, Hh2a, #Hh2lb⟩
      imod mono_list_own_alloc (GF := GF) [P0.rev - W64 1] with ⟨%γcur2, Hcur2a, #Hcur2lb⟩
      ihave #Hh20 := monoListIdxOwn_get (GF := GF) 0 (P0.rev - W64 1) rfl $$ Hh2lb
      ihave #Hcur20 := monoListIdxOwn_get (GF := GF) 0 (P0.rev - W64 1) rfl $$ Hcur2lb
      let Ppre : WsPrm GF := WsPrm.mk P0.o P0.rev P0.ctx P0.cs P0.key P0.ed P0.cn P0.pn P0.wbl
        P0.flt P0.retc P0.γret «$r0_ptr» (EtcdWatchNames.mk γr γcur γcur2 (cplOf P0)) outc recvc γr γhi γh2 dnc γdn γx
        P0.sr
      imod start_spsc (V := go_etcd_io.etcd.client.v3.WatchResponse) outc
        (rangeWatchElem (EM := V.EM) Ppre.γ V.pfx P0.o P0.rev) (fun _ => iprop(True)) γo
        $$ Houtc [Houto] with ⟨%γsp, #Hosp, Hoprod, Hocons⟩
      · iright; iexact Houto
      imod start_spsc (V := Loc) recvc (client.recvElem V Ppre) (fun _ => iprop(True)) γrc2
        $$ Hrecvc [Hrecvo] with ⟨%γrr, #Hrsp, Hrprod, Hrcons2⟩
      · ileft; iexact Hrecvo
      let P : WsPrm GF := WsPrm.mk P0.o P0.rev P0.ctx P0.cs P0.key P0.ed P0.cn P0.pn P0.wbl
        P0.flt P0.retc P0.γret «$r0_ptr» (EtcdWatchNames.mk γsp γcur γcur2 (cplOf P0)) outc recvc γrr γhi γh2 dnc γdn γx
        P0.sr
      have eq1 : (isSpsc γsp outc (rangeWatchElem (EM := V.EM) Ppre.γ V.pfx P0.o P0.rev)
          (fun _ => iprop(True)) : IProp GF) =
          isSpsc P.γ.spsc P.outc (rangeWatchElem (EM := V.EM) P.γ V.pfx P.o P.rev)
            (fun _ => iprop(True)) := rfl
      have eq2 : (isSpsc γrr recvc (client.recvElem V Ppre) (fun _ => iprop(True)) : IProp GF) =
          isSpsc P.γr P.recvc (client.recvElem V P) (fun _ => iprop(True)) := rfl
      irevert Hosp Hrsp
      rw [eq1, eq2]
      iintro #Hosp #Hrsp
      ihave #HP : iprop(wsIs V P) $$ []
      · iunfold wrRO at Hro
        icases Hro with ⟨-, -, -, -, -, -, -, -, #Rflts, -⟩
        unfold wsIs
        isplitr
        · unfold wrRO
          iframe #
        isplitr
        · iexact outc
        isplitr
        · iexact recvc
        isplitr
        · iexact donec
        isplitr
        · iexact Hosp
        isplitr
        · iexact Hrsp
        isplitr
        · iexact Hdnu
        isplitr
        · iexact Hctx
        isplitr
        · iexact Hretb
        isplitr
        · ipureintro; exact ⟨Hwsn, Hok, rfl⟩
        iexact Hsrd0
      ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
      · iPkgInit
      iunfold wgAdder at Had
      wp_apply wp_wgsWg_Add $$ [Had Htt] as ⟨Had, Hwd⟩
      · iframe
      icases client.wsElems_fresh V γs S U «$r0_ptr» _ $$ [Hels id] with ⟨%HUf, Hels, id⟩
      · iframe
      imod ghost_map_insert «$r0_ptr» () HUf $$ Hwsa with ⟨Hwsa, Hwsel⟩
      ihave Hc2p : cur2Pos P 0 0 $$ [Hcur2a]
      · unfold cur2Pos
        cases hc : cplOf P0
        · ileft; ipureintro; exact hc
        · iright
          iexists [P0.rev - W64 1], P0.rev - W64 1
          iframe Hcur2a Hh20
          ipureintro; simp
      wp_apply wp_fork_tok_self $$ [closing buf bufWaitStartTime retc HbL Hrev1 Hocons Hoprod Hcura
          Hrcons2 Hdnb Hx Hwd Hwsel Hc2p] as Htt
      · wp_apply wp_serveSub V G callSl P slice.nil bl _ rc1 γrc1
          $$ [closing buf bufWaitStartTime retc HbL Hrev1 Hocons Hoprod Hcura Hrcons2 Hdnb Hx Hwd Hwsel
            Hc2p]
          as Htok
        · unfold wgDone
          rw [show P.γ.spsc = γsp from rfl, show P.γ.cur = γcur from rfl, show P.γr = γrr from rfl,
            show P.γhi = γhi from rfl, show P.rev = P0.rev from rfl, show P.ws = «$r0_ptr» from rfl,
            show P.donec = dnc from rfl, show P.γdn = γdn from rfl, show P.γx = γx from rfl,
            show P.retc = P0.retc from rfl]
          iframe #
          iframe
          isplitr
          · unfold sliceOwn
            isplitr
            · iapply ownSlice_nil
            iapply (ownSliceCap_nil (V := Loc))
          unfold retcRes
          rw [show P.γ.spsc = γsp from rfl, show P.γ.cur = γcur from rfl, show P.rev = P0.rev from rfl,
            show P.γ.cur2 = γcur2 from rfl]
          iframe
          iframe #
        first | iexact Htok | (iframe Htok; ipureintro; simp) | (iframe Htok; ipureintro; decide)
      wp_apply wp_slice_literal (V := Loc) [«$r0_ptr»]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      iunfold sliceOwn at Hs
      icases Hs with ⟨Hs, Hscap⟩
      wp_apply wp_slice_append $$ [Hs Hscap Hsl1] as %s' ⟨Hs, Hscap, -⟩
      · iframe
      ihave %Hslen := ownSlice_len $$ Hs
      by_cases hl : S.l = []
      · have hlen1 : s'.len = W64 1 := by
          have h1 : (S.l ++ [«$r0_ptr»]).length = 1 := by rw [hl]; rfl
          have := Hslen.1; rw [h1] at this; word
        simp only [hlen1, _root_.decide_true]
        iunfold wrRO at Hro
        icases Hro with ⟨-, -, -, -, -, -, -, -, #Rflts, -⟩
        wp_take_receipt as Hrc
        wp_apply wp_toPB (wsF «$r0_ptr» go!"initReq") P0.key P0.ed P0.rev P0.pn P0.flt
          (DFrac.own (1 : Qp).half) P0.sr $$ [Hrev2] as %preq ⟨Hrev2, Hpsend⟩
        · iframe #; iframe
        imod mvcc.watchTokPool_take V.R.γ $$ Htoks Hrc with Hwt
        wp_apply HSend $$ %S.L %preq %(.create (createOf P0.key P0.ed P0.rev P0.pn P0.sr)) [Hstok Hpsend Hwt]
          as %err ⟨-, Hres⟩
        · iframe
          unfold v3rpc.watchUp
          iframe
          isplitr
          · ipureintro; simp [v3rpc.watchReqOk, createOf]
          dsimp only; iframe; simp only [createOf]; iapply client.startOk_read $$ Hsrd0
        ihave ⟨%L', %si, Hstok, %Hcase, Hupi⟩ : iprop(∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
            cliSendTok (Req := v3rpc.pbWatchRequest) γs L' ∗ ⌜client.addCase S L' si si⌝ ∗
            (match si with
             | some i => v3rpc.upAtW γs i (.create (client.createOfP P))
             | none => iprop(True))) $$ [Hres]
        · have hpend : S.pend = none := by
            cases h : S.pend with
            | none => rfl
            | some i => exact absurd hl (HgOk.2.2.2.2.2.2.2.2.2.1 i h).2.2
          ihave Hmk : iprop(∀ L2 : List v3rpc.WatchReqM,
              ⌜L2 = S.L ∨ L2 = S.L ++ [.create (createOf P0.key P0.ed P0.rev P0.pn P0.sr)]⌝ -∗
              cliSendTok (Req := v3rpc.pbWatchRequest) γs L2 -∗
              ∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
              cliSendTok (Req := v3rpc.pbWatchRequest) γs L' ∗ ⌜client.addCase S L' si si⌝ ∗
              (match si with
               | some i => v3rpc.upAtW γs i (.create (client.createOfP P))
               | none => iprop(True))) $$ []
          · iintro %L2 %HL2 Hst
            rcases HL2 with rfl | rfl
            · iexists S.L, none
              iframe
              ipureintro
              exact ⟨Or.inr (Or.inl ⟨hl, rfl, rfl, rfl⟩), trivial⟩
            · ihave ⟨Hst, #Hlb⟩ := cliSendTok_lb $$ Hst
              iexists _, some S.L.length
              iframe
              isplitr
              · ipureintro
                exact Or.inr (Or.inr ⟨hl, ⟨_, rfl⟩, rfl, rfl⟩)
              ihave Hu := upLb_at (Req := v3rpc.pbWatchRequest) γs _ S.L.length
                (.create (createOf P0.key P0.ed P0.rev P0.pn P0.sr)) (by simp) $$ Hlb
              simp only
              unfold v3rpc.upAtW
              iunfold upAt at Hu
              iexact Hu
          icases Hres with (⟨-, Htok⟩ | ⟨-, %L2, %HL2, Htok⟩)
          · iapply Hmk $$ %_ %(Or.inr rfl) Htok
          · iapply Hmk $$ %L2 %HL2 Htok
        cases err with
        | nil =>
          wp_auto
          wp_for_post
          iframe Hrcb
          iexists bo
          simp only [named]
          iframe closeErr cur backoff
          obtain ⟨Hg2, Hold2, Hnew2⟩ := client.addWs_ok (S := S) (U := U) (ws := «$r0_ptr»)
            (L' := L') (pend' := si) (si := si) HgOk Hwsn HUf Hcase
          ihave Hels := BigSepM.bigSepM_impl
              (Ψ := fun ws (_ : Unit) => client.wsElem V γs (S.addWs «$r0_ptr» L' si) ws) $$ Hels []
          · iintro !> %ws' %u %Hws' Hw'
            have Hws'' : U !! ws' = some u := Hws'
            have hne : ws' ≠ «$r0_ptr» := by
              intro e; subst e; rw [HUf] at Hws''; cases Hws''
            iapply (client.wsElem_mono V γs (S := S) (S' := S.addWs «$r0_ptr» L' si) ws' rfl
              (fun ph' h => Hold2 ws' ph' hne h)
              (fun X _ => client.create_or (by
                rcases Hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
                · exact Or.inl h
                · exact Or.inl h
                · exact Or.inr h) X)) $$ Hw'
          ihave Hels := (BigSepM.bigSepM_insert (Φ := fun ws (_ : Unit) =>
              client.wsElem V γs (S.addWs «$r0_ptr» L' si) ws) (m := U) (i := «$r0_ptr») (x := ()) HUf).2 $$ [Hels id Hrprod Hhia Hh2a Hrev2 Hupi]
          · iframe Hels
            unfold client.wsElem
            iexists P, .queued si
            isplitr
            · ipureintro; exact ⟨rfl, Hnew2⟩
            iframe HP
            simp only [WPh.id]
            iframe id
            simp only [client.wsRest, client.noCancelOk]
            rw [show P.γr = γrr from rfl, show P.γhi = γhi from rfl, show P.rev = P0.rev from rfl,
              show P.ws = «$r0_ptr» from rfl]
            iframe
            
          unfold client.runCore wgAdder
          iexists S.addWs «$r0_ptr» L' si, GMap.insert «$r0_ptr» () U, rcv, mref, s', e
          have e1 : (S.addWs «$r0_ptr» L' si).Dm = S.Dm := rfl
          have e2 : (S.addWs «$r0_ptr» L' si).L = L' := rfl
          have e3 : (S.addWs «$r0_ptr» L' si).ansd = S.ansd := rfl
          have e4 : (S.addWs «$r0_ptr» L' si).regs = S.regs := rfl
          have e5 : (S.addWs «$r0_ptr» L' si).CS = S.CS := rfl
          have e6 : (S.addWs «$r0_ptr» L' si).M = S.M := rfl
          have e7 : (S.addWs «$r0_ptr» L' si).CL = S.CL := rfl
          have e8 : (S.addWs «$r0_ptr» L' si).l = S.l ++ [«$r0_ptr»] := rfl
          rw [e1, e2, e3, e4, e5, e6, e7, e8]
          iframe
          iframe #
          isplitl [Hs Hscap]
          · unfold sliceOwn; iframe
          ipureintro; exact ⟨Hrcv, Hg2⟩
        | ok ei =>
          wp_auto
          wp_apply wp_zapError as %f1 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          wp_auto
          wp_apply wp_Debug V.lg _ _ $$ []
          · iframe #; ipureintro; exact Hlg
          wp_for_post
          iframe Hrcb
          iexists bo
          simp only [named]
          iframe closeErr cur backoff
          obtain ⟨Hg2, Hold2, Hnew2⟩ := client.addWs_ok (S := S) (U := U) (ws := «$r0_ptr»)
            (L' := L') (pend' := si) (si := si) HgOk Hwsn HUf Hcase
          ihave Hels := BigSepM.bigSepM_impl
              (Ψ := fun ws (_ : Unit) => client.wsElem V γs (S.addWs «$r0_ptr» L' si) ws) $$ Hels []
          · iintro !> %ws' %u %Hws' Hw'
            have Hws'' : U !! ws' = some u := Hws'
            have hne : ws' ≠ «$r0_ptr» := by
              intro e; subst e; rw [HUf] at Hws''; cases Hws''
            iapply (client.wsElem_mono V γs (S := S) (S' := S.addWs «$r0_ptr» L' si) ws' rfl
              (fun ph' h => Hold2 ws' ph' hne h)
              (fun X _ => client.create_or (by
                rcases Hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
                · exact Or.inl h
                · exact Or.inl h
                · exact Or.inr h) X)) $$ Hw'
          ihave Hels := (BigSepM.bigSepM_insert (Φ := fun ws (_ : Unit) =>
              client.wsElem V γs (S.addWs «$r0_ptr» L' si) ws) (m := U) (i := «$r0_ptr») (x := ()) HUf).2 $$ [Hels id Hrprod Hhia Hh2a Hrev2 Hupi]
          · iframe Hels
            unfold client.wsElem
            iexists P, .queued si
            isplitr
            · ipureintro; exact ⟨rfl, Hnew2⟩
            iframe HP
            simp only [WPh.id]
            iframe id
            simp only [client.wsRest, client.noCancelOk]
            rw [show P.γr = γrr from rfl, show P.γhi = γhi from rfl, show P.rev = P0.rev from rfl,
              show P.ws = «$r0_ptr» from rfl]
            iframe
            
          unfold client.runCore wgAdder
          iexists S.addWs «$r0_ptr» L' si, GMap.insert «$r0_ptr» () U, rcv, mref, s', e
          have e1 : (S.addWs «$r0_ptr» L' si).Dm = S.Dm := rfl
          have e2 : (S.addWs «$r0_ptr» L' si).L = L' := rfl
          have e3 : (S.addWs «$r0_ptr» L' si).ansd = S.ansd := rfl
          have e4 : (S.addWs «$r0_ptr» L' si).regs = S.regs := rfl
          have e5 : (S.addWs «$r0_ptr» L' si).CS = S.CS := rfl
          have e6 : (S.addWs «$r0_ptr» L' si).M = S.M := rfl
          have e7 : (S.addWs «$r0_ptr» L' si).CL = S.CL := rfl
          have e8 : (S.addWs «$r0_ptr» L' si).l = S.l ++ [«$r0_ptr»] := rfl
          rw [e1, e2, e3, e4, e5, e6, e7, e8]
          iframe
          iframe #
          isplitl [Hs Hscap]
          · unfold sliceOwn; iframe
          ipureintro; exact ⟨Hrcv, Hg2⟩
      · have hlen1 : ¬ (s'.len = W64 1) := by
          intro h
          have : (S.l ++ [«$r0_ptr»]).length = 1 := by
            rw [Hslen.1, h]; rfl
          simp at this; exact hl this
        simp only [hlen1, decide_false]
        wp_auto
        wp_for_post
        iframe Hrcb
        iexists bo
        simp only [named]
        iframe closeErr cur backoff
        obtain ⟨Hg2, Hold2, Hnew2⟩ := client.addWs_ok (S := S) (U := U) (ws := «$r0_ptr»)
          (L' := S.L) (pend' := S.pend) (si := none) HgOk Hwsn HUf (Or.inl ⟨hl, rfl, rfl, rfl⟩)
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => client.wsElem V γs (S.addWs «$r0_ptr» S.L S.pend) ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          have Hws'' : U !! ws' = some u := Hws'
          have hne : ws' ≠ «$r0_ptr» := by
            intro e; subst e; rw [HUf] at Hws''; cases Hws''
          iapply (client.wsElem_mono V γs (S := S) (S' := S.addWs «$r0_ptr» S.L S.pend) ws' rfl
            (fun ph' h => Hold2 ws' ph' hne h) (fun _ _ _ hi => hi)) $$ Hw'
        ihave Hels := (BigSepM.bigSepM_insert (Φ := fun ws (_ : Unit) =>
            client.wsElem V γs (S.addWs «$r0_ptr» S.L S.pend) ws) (m := U) (i := «$r0_ptr») (x := ()) HUf).2 $$ [Hels id Hrprod Hhia Hh2a Hrev2]
        · iframe Hels
          unfold client.wsElem
          iexists P, .queued none
          isplitr
          · ipureintro; exact ⟨rfl, Hnew2⟩
          iframe HP
          simp only [WPh.id]
          iframe id
          simp only [client.wsRest, client.noCancelOk]
          rw [show P.γr = γrr from rfl, show P.γhi = γhi from rfl, show P.rev = P0.rev from rfl,
            show P.ws = «$r0_ptr» from rfl]
          iframe
          
        unfold client.runCore wgAdder
        iexists S.addWs «$r0_ptr» S.L S.pend, GMap.insert «$r0_ptr» () U, rcv, mref, s', e
        have e1 : (S.addWs «$r0_ptr» S.L S.pend).Dm = S.Dm := rfl
        have e2 : (S.addWs «$r0_ptr» S.L S.pend).L = S.L := rfl
        have e3 : (S.addWs «$r0_ptr» S.L S.pend).ansd = S.ansd := rfl
        have e4 : (S.addWs «$r0_ptr» S.L S.pend).regs = S.regs := rfl
        have e5 : (S.addWs «$r0_ptr» S.L S.pend).CS = S.CS := rfl
        have e6 : (S.addWs «$r0_ptr» S.L S.pend).M = S.M := rfl
        have e7 : (S.addWs «$r0_ptr» S.L S.pend).CL = S.CL := rfl
        have e8 : (S.addWs «$r0_ptr» S.L S.pend).l = S.l ++ [«$r0_ptr»] := rfl
        rw [e1, e2, e3, e4, e5, e6, e7, e8]
        iframe
        iframe #
        isplitl [Hs Hscap]
        · unfold sliceOwn; iframe
        ipureintro; exact ⟨Hrcv, Hg2⟩
    -- respc
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, G.respc, γr.chanName
      isplit
      · ipureintro; rfl
      isplit
      · ihave #H := Hrspsc
        unfold isSpsc
        icases H with ⟨$, -⟩
      iunfold client.runCore at Hcore
      icases Hcore with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, Hcsm, Hsub, Hm, Hres, Hs, HcF, #He,
        Hstok, Hrcons, %Hrcv, #HDlb, %HgOk, Hans, Hids, #Hinfo, Hwsa, Hels, Had, Htt, Hdn⟩
      iapply spsc_rcv_au γr G.respc _ _ rcv _ $$ Hrspsc [$Hlc1 $Hlc2] Hrcons
      inext
      iintro %p %ok Hrecv
      cases ok
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hrecv with ⟨HF, -⟩
        iexfalso; iexact HF
      simp only [↓reduceIte]
      icases Hrecv with ⟨Hel, Hrcons⟩
      iunfold respcElem at Hel
      icases Hel with ⟨%m, %Lm, Hm1, HDn, #HLlb, %HLlen⟩
      iunfold v3rpc.downLbW at HDlb HLlb
      ihave %Hcmp := mono_list_lb_valid _ _ _ $$ HDlb HLlb
      have HLm : Lm = S.Dm := client.prefix_snoc_eq Hcmp (by simp at HLlen; omega)
      subst HLm
      ihave #Hspec' := Hspec
      iunfold v3rpc.watchSpec at Hspec'
      iunfold v3rpc.watchStreamSpec at Hspec'
      ihave Hwd := Hspec' $$ %(rcv.length) %m
      icases Hwd with ⟨Hto, -⟩
      rw [show ((rcv.length : Int)).toNat = rcv.length by simp] at HLlen
      irevert HDn
      rw [show ((rcv.length : Int)).toNat = rcv.length by simp]
      iintro HDn
      ihave Hwd := Hto $$ HDn
      iunfold v3rpc.watchDn at Hwd
      icases Hwd with ⟨%Hcm, Hcase⟩
      iunfold v3rpc.watchRespRecv at Hm1
      icases Hm1 with ⟨%Hpn, %h, %sl, %ps, Hhdr, Hho, Hwid, Hcr, Hca, Hcomp, Hcrs, Hfr, Hev, #Hps,
        %Hpslen, #Hevs⟩
      wp_auto
      icases Hcase with (⟨%Hsrc, Hctrl, #Hcaf⟩ | #Hmvcc)
      · iunfold v3rpc.ctrlOk at Hctrl
        icases Hctrl with ⟨%i, %req, %γo, %γa, #Haux, #Hup, %Hcans, Hcw, Hat⟩
        cases req with
        | create c =>
          obtain ⟨hs0, hev0, hcomp0, hfr0, hcr0, hcase⟩ : m.src = none ∧ m.evs = [] ∧
              m.compactRev = W64 0 ∧ m.fragment = false ∧ m.created = true ∧
              ((m.canceled = true ∧ m.watchId = W64 (-1)) ∨
               (m.canceled = false ∧ 0 ≤ sint.Z c.startRev ∧
                 (c.watchId ≠ W64 0 → m.watchId = c.watchId))) := by
            simp only [v3rpc.ctrlAnswers] at Hcans; exact Hcans
          icases client.sendTok_lookup γs S.L i (.create c) $$ [Hstok Hup] with ⟨Hstok, %HLi⟩
          · iframe; iframe #
          ihave Hfr' : iprop(⌜i ∉ S.ansd⌝ ∗ ([∗list] j ∈ S.ansd, client.ansH γs j) ∗ v3rpc.ansTok γa i)
            $$ [Hans Hat]
          · iapply client.ans_fresh
            iframe
            iframe #
          icases Hfr' with ⟨%Hia, Hans, Hat⟩
          have hpend : S.pend = some i := (HgOk.2.2.2.2.2.2.2.1 i c HLi).resolve_left Hia
          have hlne : S.l ≠ [] := (HgOk.2.2.2.2.2.2.2.2.2.1 i hpend).2.2
          obtain ⟨h0, hh0⟩ : ∃ h0, S.l.head? = some h0 := by
            cases hl : S.l with
            | nil => exact absurd hl hlne
            | cons x xs => exact ⟨x, rfl⟩
          -- the response's header and events
          iunfold v3rpc.hdrOwn at Hho
          icases Hho with ⟨%Hhn, Hh1, Hh2, Hhrev, Hh4, Hh5⟩
          ipersist Hhrev
          ihave #Hha : iprop(hdrAt h m.hdr.revision) $$ []
          · unfold hdrAt; iright; iframe Hhrev; ipureintro; exact Hhn
          ihave ⟨%kvs, %Hkvl, #Hea, -⟩ := client.evs_eventsAt sl ps m.evs Hpslen $$ [Hps Hevs]
          · iframe #
          ihave #Hea0 : iprop(eventsAt sl ([] : List EvModel)) $$ []
          · have : List.zipWith client.evModelOf m.evs kvs = [] := by rw [hev0]; simp
            rw [← this]; iexact Hea
          -- the new id's token and watcher (unless the create was refused)
          ihave Hidp : iprop(⌜m.canceled = false → m.watchId ∉ S.regs⌝ ∗
              ([∗list] X ∈ S.regs, client.idH γs X) ∗
              ([∗list] X ∈ (if m.canceled then [] else [m.watchId]), client.idH γs X) ∗
              □ (⌜m.canceled = false⌝ -∗ ∃ (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat),
                ⌜v3rpc.createRangeOk c m.watchId rg⌝ ∗ mvcc.watcherIs V.R.γ w rg fcs lo ∗
                fcs ↦*□ ([] : List GoFunc) ∗
                (∃ γw : mvcc.WatcherNames, mvcc.watcherMeta V.R.γ w γw ∗ ⌜γw.sr = c.sr⌝) ∗
                ∃ (γo : mvcc.WsStreamNames) (γa : GName), streamAuxIs γs (v3rpc.auxOf γo γa) ∗
                  mvcc.idAssigned γo m.watchId w)) $$ [Hcw Hids]
          · cases hcan : m.canceled
            · irevert Hcw
              simp only [v3rpc.ctrlWatcher, hcan, Bool.false_eq_true, ↓reduceIte]
              iintro ⟨%w, %rg, %fcs, %lo, %Hcrg, #Hwi, #Hfcs, #Hws, #Hias, Hidt, -⟩
              ihave ⟨%HXr, Hids, Hidt⟩ := client.id_fresh γs S.regs m.watchId γo γa $$ [Hids Hidt]
              · iframe; iframe #
              isplitr
              · ipureintro; intro _; exact HXr
              iframe Hids
              isplitl [Hidt]
              · iapply BigSepL.bigSepL_singleton.2
                unfold client.idH
                iexists γo, γa
                iframe; iframe #
              imodintro
              iintro %-
              iexists w, rg, fcs, lo
              iframe #
              ipureintro; exact Hcrg
            · iframe Hids
              isplitr
              · ipureintro; intro h'; cases h'
              isplitr
              · simp only [↓reduceIte]; iapply BigSepL.bigSepL_nil.2; itrivial
              imodintro
              iintro %h'; cases h'
          icases Hidp with ⟨%HXf, Hids, Hidn, #Hwf⟩
          ihave #Hsf2 := Hsf
          iunfold watchSrvFacts at Hsf2
          icases Hsf2 with ⟨-, #Hcf⟩
          ihave ⟨%hMf, Hels⟩ : iprop(⌜S.M !! m.watchId = none ∨
              (m.watchId ∈ S.regs ∧ m.watchId ≠ W64 (-1))⌝ ∗
              [∗map] ws ↦ _u ∈ U, client.wsElem V γs S ws) $$ [Hels]
          · cases hMX : S.M !! m.watchId with
            | none => iframe; ipureintro; left; rfl
            | some ws1 =>
              icases client.M_entry_facts V γs HgOk hMX $$ Hels with ⟨%Hf, Hels⟩
              iframe; ipureintro; right; exact Hf
          rw [hcr0]
          wp_auto
          iunfold sliceOwn at Hs
          icases Hs with ⟨Hs, Hscap⟩
          ihave %Hsll := ownSlice_len $$ Hs
          have hlen0 : S.l.length ≠ 0 := fun h => hlne (List.length_eq_zero_iff.1 h)
          have hl0 : S.l[0]? = some h0 := by
            cases hl : S.l with
            | nil => exact absurd hl hlne
            | cons x xs => rw [hl] at hh0; simpa using hh0
          wp_bind (If _ _ _)
          iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
              ∃ (S1 : client.RunSt) (e' : GoInterface),
              ⌜client.gOk S1 U ∧ S1.pend = none ∧ S1.L = S.L ∧ S1.Dm = S.Dm ++ [m] ∧
                S1.CL = S.CL ∧ S1.CS = S.CS⌝ ∗
              wgsF G.wgs go!"substreams" ↦ mref ∗ ownMap mref (DFrac.own 1) S1.M ∗
              wgsF G.wgs go!"resuming" ↦ s ∗ s ↦* S1.l ∗ ownSliceCap Loc s (DFrac.own 1) ∗
              wgsF G.wgs go!"closeErr" ↦ e' ∗ statusErrOk e' ∗
              ([∗list] j ∈ S1.ansd, client.ansH γs j) ∗ ([∗list] X ∈ S1.regs, client.idH γs X) ∗
              ([∗map] ws ↦ _u ∈ U, client.wsElem V γs S1 ws))))
          isplitl [pbresp Hsub Hm Hres Hs Hscap HcF Hans Hids Hidn Hels Hat Hwid Hca Hcrs Hhdr Hcr Hcomp Hfr Hev]
          · have hpos : 0 < sint.Z s.len := by
              have h1 := Hsll.1; have h2 : 0 < S.l.length := Nat.pos_of_ne_zero hlen0; word
            have hlen : s.len ≠ W64 0 := by intro e0; rw [e0] at hpos; simp at hpos
            have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := ⟨by simp, by simpa using hpos⟩
            simp only [hlen, decide_false, Bool.not_false]
            wp_auto
            rw [ite_eq_left Hbnd]
            wp_apply wp_load_slice_index s (sint.Z (W64 0)) S.l (DFrac.own 1) h0 (by simp) $$ [Hs] as Hs
            · iframe; ipureintro; simpa using hl0
            by_cases hn0 : h0 = null
            · subst hn0
              simp only [_root_.decide_true, Bool.not_true]
              wp_auto
              obtain ⟨Hg1, Hold1, -⟩ := client.answer_ok (U := U) (reg := false) HgOk hpend hh0 hs0
                hcr0 rfl HXf (fun hc => by rcases hcase with ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all) (fun h => by cases h) (fun h => by cases h) (fun h => absurd rfl h)
              isplitr
              · first | itrivial | (ipureintro; rfl)
              iexists S.answer m i m.watchId null false, e
              have e1 : (S.answer m i m.watchId null false).M = S.M := by simp [client.RunSt.answer]
              have e2 : (S.answer m i m.watchId null false).l = S.l := by simp [client.RunSt.answer]
              have e3 : (S.answer m i m.watchId null false).ansd = S.ansd ++ [i] := rfl
              have e4 : (S.answer m i m.watchId null false).regs =
                  (if m.canceled then S.regs else S.regs ++ [m.watchId]) := rfl
              rw [e1, e2, e3, e4]
              isplitr
              · ipureintro; exact ⟨Hg1, rfl, rfl, rfl, rfl, rfl⟩
              iframe
              iframe #
              isplitl [Hat]
              · iapply BigSepL.bigSepL_singleton.2
                unfold client.ansH
                iexists γo, γa
                iframe; iframe #
              isplitl [Hids Hidn]
              · iapply client.regs_join; iframe
              ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                  client.wsElem V γs (S.answer m i m.watchId null false) ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : U !! ws' = some u := Hws'
                cases u
                have hne : ws' ≠ null := fun e => by
                  subst e; rw [HgOk.2.2.2.2.2.1] at Hws''; cases Hws''
                iapply (client.wsElem_mono' V γs (S := S) (S' := S.answer m i m.watchId null false) ws'
                  (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                  (fun ph h => Hold1 ws' ph hne Hws'' h) rfl) $$ Hw'
              iexact Hels
            simp only [hn0, decide_false, Bool.not_false]
            wp_auto
            have hmem0 : h0 ∈ S.l := List.mem_of_getElem? hl0
            have hU0 : U !! h0 = some () := HgOk.2.2.1 h0 hmem0 hn0
            icases (BigSepM.bigSepM_delete hU0).1 $$ Hels with ⟨Hw, Hels⟩
            iunfold client.wsElem at Hw
            icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
            ihave %HPq : ⌜wsReqOk V.pfx P ∧ P.γ.cpl = cplOf P⌝ $$ []
            · ihave #HP' := HP
              iunfold wsIs at HP'
              icases HP' with ⟨-, -, -, -, -, -, -, -, -, %Hq, -⟩
              ipureintro; exact ⟨Hq.2.1, Hq.2.2⟩
            subst HPws
            obtain ⟨si, rfl, hsi⟩ : ∃ si, ph = .queued si ∧ si = some i := by
              cases ph with
              | queued si =>
                refine ⟨si, rfl, ?_⟩
                cases si with
                | none => have := Hph.2.2.2.2 rfl hh0; rw [hpend] at this; cases this
                | some i' => have := (Hph.2.2.2.1 i' rfl).1; rw [hpend] at this; cases this; rfl
              | reg X => exact absurd hmem0 Hph.2.1
              | closedRun X => exact absurd hmem0 Hph.2.1
              | orphan => exact absurd hmem0 Hph.2.1
            subst hsi
            iunfold client.wsRest at Hrest
            icases Hrest with ⟨Hprod, Hauth, Hauth2, Hrv, #Hupi⟩
            ihave #Hu1 := Hup
            iunfold v3rpc.upAtW at Hu1 Hupi
            ihave %Hceq := mono_list_idx_agree _ _ _ _ $$ Hu1 Hupi
            have hc : c = client.createOfP P := by injection Hceq
            subst hc
            by_cases hfail : addFails m.watchId m.canceled m.cancelReason
            · wp_apply wp_addSub V G.wgs p P.ws m.watchId m.canceled m.cancelReason (DFrac.own 1)
                (DFrac.own 1) (W64 (-1)) mref S.M e $$ [Hwid Hca Hcrs Hid Hsub Hm HcF Hprod]
                as ⟨Hwid, Hca, Hcrs, Hsub, Hpost⟩
              · iframe; iframe #
                iintro %-
                unfold recvcCloser
                iexists P, []
                iframe; iframe #
                ipureintro; rfl
              irevert Hpost
              rw [show decide (addFails m.watchId m.canceled m.cancelReason) = true from
                decide_eq_true hfail]
              simp only [↓reduceIte]
              iintro ⟨Hid, Hm, %e', HcF, #He'⟩
              have hXm : m.watchId = W64 (-1) := by
                rcases hfail with h | ⟨hca, -⟩
                · exact h
                · rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
                  · exact h
                  · rw [hca] at h; cases h
              have hMn : S.M !! m.watchId = none := hMf.resolve_right (fun h => h.2 hXm)
              ihave Hrf : iprop(respFields p (DFrac.own 1) m h sl) $$ [Hhdr Hwid Hcr Hca Hcomp Hcrs Hfr Hev]
              · unfold respFields
                rw [hcr0]
                iframe
                ipureintro; exact Hhn
              have hnb : ¬ client.isBroadcast m := fun h => by
                obtain ⟨-, -, h3, -⟩ := h; rw [hcr0] at h3; cases h3
              wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl [] mref S.M (DFrac.own 1)
                (DFrac.own 1) (fun _ => client.dummyWsPrm G γr) (fun _ => [])
                $$ [Hrf Hsub Hm] as %b ⟨Hrf, Hsub, Hm, Hpost⟩
              · iframe
                iframe #
                isplitr
                · ipureintro; simp [hev0]
                isplitr
                · iintro %-; itrivial
                rw [if_neg (by simpa using hnb), hMn]
                itrivial
              rw [ite_eq_left Hbnd]
              wp_apply wp_store_slice_index s (sint.Z (W64 0)) S.l null $$ [Hs] as Hs
              · iframe; ipureintro; exact ⟨by simp, by have := Hsll.1; word⟩
              obtain ⟨Hg1, Hold1, Hnew1⟩ := client.answer_ok (U := U) (reg := false) HgOk hpend hh0 hs0
                hcr0 rfl HXf (fun hc => by rcases hcase with ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all) (fun h => by cases h) (fun h => by cases h) (fun _ => Hph)
              isplitr
              · first | itrivial | (ipureintro; rfl)
              iexists S.answer m i m.watchId P.ws false, e'
              have e1 : (S.answer m i m.watchId P.ws false).M = S.M := by simp [client.RunSt.answer]
              have e2 : (S.answer m i m.watchId P.ws false).l = S.l.set (sint.Z (W64 0)).toNat null := by
                simp [client.RunSt.answer, hn0]
              have e3 : (S.answer m i m.watchId P.ws false).ansd = S.ansd ++ [i] := rfl
              have e4 : (S.answer m i m.watchId P.ws false).regs =
                  (if m.canceled then S.regs else S.regs ++ [m.watchId]) := rfl
              rw [e1, e2, e3, e4]
              isplitr
              · ipureintro; exact ⟨Hg1, rfl, rfl, rfl, rfl, rfl⟩
              iframe
              iframe #
              isplitl [Hat]
              · iapply BigSepL.bigSepL_singleton.2
                unfold client.ansH
                iexists γo, γa
                iframe; iframe #
              isplitl [Hids Hidn]
              · iapply client.regs_join; iframe
              ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                  client.wsElem V γs (S.answer m i m.watchId P.ws false) ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                have hne : ws' ≠ P.ws := by
                  intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
                cases u
                iapply (client.wsElem_mono' V γs (S := S) (S' := S.answer m i m.watchId P.ws false) ws'
                  (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                  (fun ph h => Hold1 ws' ph hne Hws'' h) rfl) $$ Hw'
              iapply (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                client.wsElem V γs (S.answer m i m.watchId P.ws false) ws) (m := U) (i := P.ws) (x := ()) hU0).2
              iframe Hels
              unfold client.wsElem
              iexists P, .orphan
              isplitr
              · ipureintro; exact ⟨rfl, by simpa using Hnew1 hn0⟩
              iframe HP
              simp only [WPh.id, client.wsRest, client.noCancelOk]
              iframe Hid
              try itrivial
            · have hca : m.canceled = false := by
                cases hcan : m.canceled
                · rfl
                · exfalso; apply hfail
                  rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
                  · left; exact h
                  · rw [hcan] at h; cases h
              have hXn : m.watchId ≠ W64 (-1) := fun h => hfail (Or.inl h)
              have hXr : m.watchId ∉ S.regs := HXf hca
              have hMn : S.M !! m.watchId = none := hMf.resolve_right (fun h => hXr h.1)
              wp_apply wp_addSub V G.wgs p P.ws m.watchId m.canceled m.cancelReason (DFrac.own 1)
                (DFrac.own 1) (W64 (-1)) mref S.M e $$ [Hwid Hca Hcrs Hid Hsub Hm HcF]
                as ⟨Hwid, Hca, Hcrs, Hsub, Hpost⟩
              · iframe; iframe #
                iintro %h'; exact absurd h' hfail
              irevert Hpost
              rw [show decide (addFails m.watchId m.canceled m.cancelReason) = false from
                decide_eq_false hfail]
              simp only [Bool.false_eq_true, ↓reduceIte]
              iintro ⟨Hid, Hm, HcF⟩
              -- the watcher the server registered
              ihave ⟨%w, %rg, %fcs, %lo, %Hcrg, #Hwi, #Hfcs, #Hws, %γo', %γa', #Hax', #Hias⟩ := Hwf $$ %hca
              ihave #Hwi' := Hwi
              iunfold mvcc.watcherIs at Hwi'
              icases Hwi' with ⟨%γw0, %C0, -, #Hwfix, -⟩
              ihave %Hfresh := client.evsSoFar_fresh m.watchId w rg fcs HgOk hXr hXn Hcrg.2.2.1
                $$ [Hinfo Hwfix]
              · iframe #
              -- the cursors: one more, the same
              imod monoListAuthOwn_update_app (γ := P.γhi) (l := [P.rev - W64 1]) [P.rev - W64 1]
                $$ Hauth with ⟨Hauth, #Hlb⟩
              ihave #Hi0 := monoListIdxOwn_get (γ := P.γhi) 0 (P.rev - W64 1) (by simp) $$ Hlb
              ihave #Hi1 := monoListIdxOwn_get (γ := P.γhi) 1 (P.rev - W64 1) (by simp) $$ Hlb
              -- (K2e-7d) the second cursor: one more, the same
              imod monoListAuthOwn_update_app (γ := P.γh2) (l := [P.rev - W64 1]) [P.rev - W64 1]
                $$ Hauth2 with ⟨Hauth2, #Hlb2⟩
              ihave #Hj0 := monoListIdxOwn_get (γ := P.γh2) 0 (P.rev - W64 1) (by simp) $$ Hlb2
              ihave #Hj1 := monoListIdxOwn_get (γ := P.γh2) 1 (P.rev - W64 1) (by simp) $$ Hlb2
              ihave #Hcm0 : client.recvCmpl V P 0 (client.wrOf m h sl)
                  ⟨[], W64 0, false, true, m.hdr.revision⟩ $$ []
              · unfold client.recvCmpl
                cases hcp : P.γ.cpl
                · ileft; ipureintro; rfl
                iright
                iexists P.rev - W64 1, P.rev - W64 1
                simp only [Int.toNat_zero, Nat.zero_add]
                iframe Hj0 Hj1
                unfold watchRespOk
                iright; ileft
                ipureintro
                refine ⟨?_, rfl, by simp [RespModel.isProgressNotify], rfl⟩
                unfold watchErr client.wrOf; simp [hcomp0, hca]
              ihave Hrf : iprop(respFields p (DFrac.own 1) m h sl) $$ [Hhdr Hwid Hcr Hca Hcomp Hcrs Hfr Hev]
              · unfold respFields
                rw [hcr0]
                iframe
                ipureintro; exact Hhn
              have hnb : ¬ client.isBroadcast m := fun h => by
                obtain ⟨-, -, h3, -⟩ := h; rw [hcr0] at h3; cases h3
              wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl [] mref (GMap.insert m.watchId P.ws S.M)
                (DFrac.own 1) (DFrac.own 1) (fun _ => P) (fun _ => [])
                $$ [Hrf Hsub Hm Hprod Hrv] as %b ⟨Hrf, Hsub, Hm, Hpost⟩
              · iframe
                iframe #
                isplitr
                · ipureintro; simp [hev0]
                isplitr
                · iintro %-; itrivial
                rw [if_neg (by simpa using hnb), GMap.lookup_insert]
                isplitr
                · ipureintro; rfl
                unfold sendCap
                iframe
                iframe #
                iintro %wr #Hwr
                iapply client.recvElem_created V P m h sl (P.rev - W64 1) P.rev wr ⟨hcomp0, hca, hcr0⟩ Hhn
                iframe
                iframe #
              irevert Hpost
              rw [if_neg (show ¬ (decide (client.isBroadcast m) = true) by
                simp only [decide_eq_true_eq]; exact hnb)]
              iintro ⟨%wr, Hpost⟩
              ihave #Hsnap : iprop(client.regSnap γs S.Dm w) $$ []
              · irevert Hcaf
                unfold v3rpc.createdAfter
                rw [hcr0, hca]
                simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
                iintro #Hcaf
                icases Hcaf with ⟨%γo2, %γa2, %w2, %l0, %l, %L, %n, #Hax2, #Hia2, #Hl0, #Hl, #HL,
                  #Hrn, %Hn, %Hpp⟩
                ihave %He : iprop(⌜v3rpc.auxOf γo' γa' = v3rpc.auxOf γo2 γa2⌝) $$ []
                · iapply streamAuxIs_agree
                  isplit
                  · iexact Hax'
                  · iexact Hax2
                obtain ⟨rfl, rfl⟩ := v3rpc.auxOf_inj He
                ihave %Hw := mvcc.idAssigned_agree γo' m.watchId w w2 $$ [Hias Hia2]
                · isplit
                  · iexact Hias
                  · iexact Hia2
                subst Hw
                ihave #HL' := HL
                iunfold v3rpc.downLbW at HL'
                ihave %HcL := mono_list_lb_valid _ _ _ $$ HDlb HL'
                have hLD : L = S.Dm := by
                  have hl : L.length = S.Dm.length := by rw [Hpp.2.1]; exact Hrcv
                  rcases HcL with h' | h'
                  · exact (h'.eq_of_length hl.symm).symm
                  · exact h'.eq_of_length hl
                unfold client.regSnap
                iexists γo', γa', l, L, n
                iframe Hax' Hl Hrn
                ipureintro
                exact ⟨Nat.le_trans Hn Hpp.1.length_le, by rw [hLD]; exact List.prefix_refl _, Hpp.2.2⟩
              ihave #Hrg : iprop(client.regFacts V γs S.Dm P m.watchId w rg fcs lo) $$ []
              · unfold client.regFacts
                iframe Hwi Hfcs Hsnap
                isplitr
                · ipureintro; exact Hcrg
                isplitr
                · icases Hws with ⟨%γw', #Hm', %Hsr'⟩
                  iexists γw'; iframe Hm'; ipureintro; exact Hsr'
                iexists γo', γa'
                iframe Hax' Hias
              ihave Hpend : iprop(|==> client.cur2Pend V γs (S.Dm ++ [m]) P m.watchId w rg lo []
                  ([P.rev - W64 1] ++ [P.rev - W64 1])) $$ [Hauth2]
              · unfold client.cur2Pend
                cases hcp : P.γ.cpl
                · imodintro; iframe Hauth2; ileft; ipureintro; rfl
                obtain ⟨-, hrev1, -, hstart, -⟩ := client.cpl_facts V P m.watchId rg HPq.1 HPq.2 hcp Hcrg
                ihave %Hlo := client.cpl_lo V w rg fcs lo P.rev hstart hrev1 $$ Hwi
                have hE : client.evsOf (S.Dm ++ [m]) w = [] := by
                  have := client.evsSoFar_snoc_ctrl S.Dm m w hs0
                  rw [Hfresh] at this; exact this
                imod client.cur2Ok_init V γs P (S.Dm ++ [m]) m.watchId w rg lo hrev1 Hlo hE with #Hc0
                imodintro
                iframe Hauth2
                iright; iright
                isplitr
                · ipureintro; rfl
                iexists P.rev - W64 1
                iframe Hc0
                ipureintro; rfl
              imod Hpend with Hpend
              ihave Hrest := client.reg_post V γs P S.Dm m m.watchId w rg fcs lo []
                ([P.rev - W64 1] ++ [P.rev - W64 1]) ([P.rev - W64 1] ++ [P.rev - W64 1]) b wr
                $$ [Hauth Hpost Hpend]
              · iframe
                iframe #
                iright
                isplitr
                · ipureintro; rfl
                iexists P.rev - W64 1
                isplitr
                · ipureintro; rfl
                unfold client.cursorOk
                rw [client.evsSoFar_snoc_ctrl S.Dm m w hs0, Hfresh]
                isplitr
                · ipureintro; left; exact ⟨rfl, rfl⟩
                ileft; ipureintro; rfl
              rw [ite_eq_left Hbnd]
              wp_apply wp_store_slice_index s (sint.Z (W64 0)) S.l null $$ [Hs] as Hs
              · iframe; ipureintro; exact ⟨by simp, by have := Hsll.1; word⟩
              obtain ⟨Hg1, Hold1, Hnew1⟩ := client.answer_ok (U := U) (reg := true) HgOk hpend hh0 hs0
                hcr0 rfl HXf (fun hc => by rcases hcase with ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all) (fun _ => hMn) (fun _ => ⟨hn0, hXn, hca⟩) (fun _ => Hph)
              isplitr
              · first | itrivial | (ipureintro; rfl)
              iexists S.answer m i m.watchId P.ws true, e
              have e1 : (S.answer m i m.watchId P.ws true).M = GMap.insert m.watchId P.ws S.M := by simp [client.RunSt.answer]
              have e2 : (S.answer m i m.watchId P.ws true).l = S.l.set (sint.Z (W64 0)).toNat null := by
                simp [client.RunSt.answer, hn0]
              have e3 : (S.answer m i m.watchId P.ws true).ansd = S.ansd ++ [i] := rfl
              have e4 : (S.answer m i m.watchId P.ws true).regs =
                  (if m.canceled then S.regs else S.regs ++ [m.watchId]) := rfl
              rw [e1, e2, e3, e4]
              isplitr
              · ipureintro; exact ⟨Hg1, rfl, rfl, rfl, rfl, rfl⟩
              iframe
              iframe #
              isplitl [Hat]
              · iapply BigSepL.bigSepL_singleton.2
                unfold client.ansH
                iexists γo, γa
                iframe; iframe #
              isplitl [Hids Hidn]
              · iapply client.regs_join; iframe
              ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                  client.wsElem V γs (S.answer m i m.watchId P.ws true) ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                have hne : ws' ≠ P.ws := by
                  intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
                cases u
                iapply (client.wsElem_mono' V γs (S := S) (S' := S.answer m i m.watchId P.ws true) ws'
                  (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                  (fun ph h => Hold1 ws' ph hne Hws'' h) rfl) $$ Hw'
              iapply (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                client.wsElem V γs (S.answer m i m.watchId P.ws true) ws) (m := U) (i := P.ws) (x := ()) hU0).2
              iframe Hels
              unfold client.wsElem
              iexists P, .reg m.watchId
              isplitr
              · ipureintro; exact ⟨rfl, by simpa using Hnew1 hn0⟩
              iframe HP
              simp only [WPh.id]
              iframe Hid
              rw [show (S.answer m i m.watchId P.ws true).Dm = S.Dm ++ [m] from rfl]
              iframe Hrest
              -- a fresh id: no cancel request for it was sent (a cancel's id is registered)
              unfold client.noCancelOk
              ileft; ipureintro
              intro j hj
              exact hXr (HgOk.2.2.2.2.2.2.2.2.1 j m.watchId hj)
          iintro %v ⟨%Hv, %S1, %e1, ⟨%Hg1, %Hp1, %HL1, %HD1, %HCL1, %HCS1⟩, Hsub, Hm, Hres, Hs, Hscap,
            HcF, #He1, Hans, Hids, Hels⟩
          subst Hv
          wp_auto
          wp_apply wp_nextResume G.wgs s S1.l $$ [Hres Hs Hscap] as %ws2 ⟨%s2, Hres, Hs, %Hws2⟩
          · iframe #; unfold sliceOwn; iframe
          by_cases hn2 : ws2 = null
          · simp only [hn2, _root_.decide_true, Bool.not_true]
            have hhd : (S1.l.dropWhile (fun x => decide (x = null))).head? = none := by
              cases hd : (S1.l.dropWhile (fun x => decide (x = null))).head? with
              | none => rfl
              | some x =>
                exfalso
                have hx := client.dropNull_head hd
                rw [hd] at Hws2; simp at Hws2; exact hx (Hws2 ▸ hn2)
            obtain ⟨Hg2, Hold2, -⟩ := client.resume_ok (si := none) (U := U) Hg1 Hp1
              (Or.inl ⟨rfl, rfl, rfl⟩)
            ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                client.wsElem V γs (S1.resume S1.L none) ws) $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              have Hws'' : U !! ws' = some u := Hws'
              cases u
              iapply (client.wsElem_mono V γs (S := S1) (S' := S1.resume S1.L none) ws' rfl
                (fun ph h => Hold2 ws' ph Hws'' (by rw [hhd]; simp) h) (fun _ _ _ hi => hi)) $$ Hw'
            wp_auto
            wp_for_post
            iframe Hrcb
            iexists bo
            simp only [named]
            iframe closeErr cur backoff
            unfold client.runCore
            iexists S1.resume S1.L none, U, rcv ++ [p], mref, s2, e1
            have r1 : (S1.resume S1.L none).Dm = S.Dm ++ [m] := HD1
            have r2 : (S1.resume S1.L none).M = S1.M := rfl
            have r3 : (S1.resume S1.L none).l = S1.l.dropWhile (fun x => decide (x = null)) := rfl
            have r4 : (S1.resume S1.L none).CL = S.CL := HCL1
            have r5 : (S1.resume S1.L none).CS = S.CS := HCS1
            have r6 : (S1.resume S1.L none).L = S1.L := rfl
            have r7 : (S1.resume S1.L none).ansd = S1.ansd := rfl
            have r8 : (S1.resume S1.L none).regs = S1.regs := rfl
            rw [r1, r2, r3, r4, r5, r6, r7, r8]
            rw [HL1]
            iframe
            iframe #
            isplitr
            · ipureintro; simp [Hrcv]
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; first | exact Hg2 | (rw [← HL1]; exact Hg2)
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial
          simp only [hn2, decide_false, Bool.not_false]
          have hhd : (S1.l.dropWhile (fun x => decide (x = null))).head? = some ws2 := by
            cases hd : (S1.l.dropWhile (fun x => decide (x = null))).head? with
            | none => rw [hd] at Hws2; simp at Hws2; exact absurd Hws2 hn2
            | some x => rw [hd] at Hws2; simp at Hws2; rw [Hws2]
          have hmem2 : ws2 ∈ S1.l :=
            (client.mem_dropNull hn2).1 (List.mem_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd))
          have hU2 : U !! ws2 = some () := Hg1.2.2.1 ws2 hmem2 hn2
          icases (BigSepM.bigSepM_delete hU2).1 $$ Hels with ⟨Hw, Hels⟩
          iunfold client.wsElem at Hw
          icases Hw with ⟨%P2, %ph2, ⟨%HPws2, %Hph2⟩, #HP2, Hid2, Hrest2, #Hnc2⟩
          subst HPws2
          obtain ⟨si2, rfl⟩ : ∃ si2, ph2 = .queued si2 := by
            cases ph2 with
            | queued si => exact ⟨si, rfl⟩
            | reg X => exact absurd hmem2 Hph2.2.1
            | closedRun X => exact absurd hmem2 Hph2.2.1
            | orphan => exact absurd hmem2 Hph2.2.1
          iunfold client.wsRest at Hrest2
          icases Hrest2 with ⟨Hprod2, Hauth2, Hh2a2, Hrv2, -⟩
          ihave #HP2' := HP2
          iunfold wsIs at HP2'
          icases HP2' with ⟨#Hro2, -⟩
          iunfold wrRO at Hro2
          icases Hro2 with ⟨-, #Rkey, #Rend, -, #Rpn, #Rfrag, -, #Rflt, #Rflts, #Rprev⟩
          wp_take_receipt as Hrc
          wp_apply wp_toPB (wsF P2.ws go!"initReq") P2.key P2.ed P2.rev P2.pn P2.flt
            (DFrac.own (1 : Qp).half) P2.sr $$ [Hrv2] as %preq ⟨Hrv2, Hpsend⟩
          · iframe #; iframe
          imod mvcc.watchTokPool_take V.R.γ $$ Htoks Hrc with Hwt
          wp_apply HSend $$ %S.L %preq %(.create (createOf P2.key P2.ed P2.rev P2.pn P2.sr)) [Hstok Hpsend Hwt]
            as %err ⟨-, Hres'⟩
          · iframe
            unfold v3rpc.watchUp
            iframe
            isplitr
            · ipureintro; simp [v3rpc.watchReqOk, createOf]
            dsimp only; iframe
            ihave #HP2s := HP2
            iunfold wsIs at HP2s
            icases HP2s with ⟨-, -, -, -, -, -, -, -, -, -, #Hsrd2⟩
            simp only [createOf]; iapply client.startOk_read $$ Hsrd2
          ihave ⟨%L', %si, Hstok, %Hcase, Hupi⟩ : iprop(∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
              cliSendTok (Req := v3rpc.pbWatchRequest) γs L' ∗
              ⌜(L' = S1.L ∧ si = none ∧ si = none) ∨
                ((∃ c, L' = S1.L ++ [.create c]) ∧ si = some S1.L.length ∧ si = some S1.L.length ∧
                  S1.l.dropWhile (fun y => decide (y = null)) ≠ [])⌝ ∗
              (match si with
               | some i => v3rpc.upAtW γs i (.create (client.createOfP P2))
               | none => iprop(True))) $$ [Hres']
          · have hne2 : S1.l.dropWhile (fun y => decide (y = null)) ≠ [] := by
              intro e0; rw [e0] at hhd; simp at hhd
            ihave Hmk : iprop(∀ L2 : List v3rpc.WatchReqM,
                ⌜L2 = S.L ∨ L2 = S.L ++ [.create (createOf P2.key P2.ed P2.rev P2.pn P2.sr)]⌝ -∗
                cliSendTok (Req := v3rpc.pbWatchRequest) γs L2 -∗
                ∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
                cliSendTok (Req := v3rpc.pbWatchRequest) γs L' ∗
                ⌜(L' = S1.L ∧ si = none ∧ si = none) ∨
                  ((∃ c, L' = S1.L ++ [.create c]) ∧ si = some S1.L.length ∧ si = some S1.L.length ∧
                    S1.l.dropWhile (fun y => decide (y = null)) ≠ [])⌝ ∗
                (match si with
                 | some i => v3rpc.upAtW γs i (.create (client.createOfP P2))
                 | none => iprop(True))) $$ []
            · iintro %L2 %HL2 Hst
              rw [← HL1] at HL2
              rcases HL2 with rfl | rfl
              · iexists S1.L, none
                iframe
                isplitr
                · ipureintro; exact Or.inl ⟨rfl, rfl, rfl⟩
                itrivial
              · ihave ⟨Hst, #Hlb⟩ := cliSendTok_lb $$ Hst
                iexists _, some S1.L.length
                iframe
                isplitr
                · ipureintro
                  exact Or.inr ⟨⟨_, rfl⟩, rfl, rfl, hne2⟩
                ihave Hu := upLb_at (Req := v3rpc.pbWatchRequest) γs _ S1.L.length
                  (.create (createOf P2.key P2.ed P2.rev P2.pn P2.sr)) (by simp) $$ Hlb
                simp only
                unfold v3rpc.upAtW
                iunfold upAt at Hu
                iexact Hu
            icases Hres' with (⟨-, Htok⟩ | ⟨-, %L2, %HL2, Htok⟩)
            · iapply Hmk $$ %_ %(Or.inr rfl) Htok
            · iapply Hmk $$ %L2 %HL2 Htok
          obtain ⟨Hg2, Hold2, Hnew2⟩ := client.resume_ok (U := U) (L' := L') (pend' := si) (si := si)
            Hg1 Hp1 Hcase
          ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
              client.wsElem V γs (S1.resume L' si) ws) $$ Hels []
          · iintro !> %ws' %u %Hws' Hw'
            have Hws'' : (GMap.delete P2.ws U) !! ws' = some u := Hws'
            have hne : ws' ≠ P2.ws := by
              intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
            rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
            cases u
            iapply (client.wsElem_mono V γs (S := S1) (S' := S1.resume L' si) ws' rfl
              (fun ph h => Hold2 ws' ph Hws'' (by rw [hhd]; intro e; exact hne (Option.some.inj e).symm) h)
              (fun X _ => client.create_or (by
                rcases Hcase with ⟨h, -⟩ | ⟨h, -⟩
                · exact Or.inl h
                · exact Or.inr h) X))
              $$ Hw'
          ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
              client.wsElem V γs (S1.resume L' si) ws) (m := U) (i := P2.ws) (x := ()) hU2).2
              $$ [Hels Hid2 Hprod2 Hauth2 Hh2a2 Hrv2 Hupi]
          · iframe Hels
            unfold client.wsElem
            iexists P2, .queued si
            isplitr
            · ipureintro; exact ⟨rfl, Hnew2 P2.ws hhd hU2 _ Hph2⟩
            iframe HP2
            simp only [WPh.id]
            iframe Hid2
            simp only [client.wsRest, client.noCancelOk]
            iframe
          cases err with
          | nil =>
            wp_auto
            wp_for_post
            iframe Hrcb
            iexists bo
            simp only [named]
            iframe closeErr cur backoff
            unfold client.runCore
            iexists S1.resume L' si, U, rcv ++ [p], mref, s2, e1
            have r1 : (S1.resume L' si).Dm = S.Dm ++ [m] := HD1
            have r2 : (S1.resume L' si).M = S1.M := rfl
            have r3 : (S1.resume L' si).l = S1.l.dropWhile (fun x => decide (x = null)) := rfl
            have r4 : (S1.resume L' si).CL = S.CL := HCL1
            have r5 : (S1.resume L' si).CS = S.CS := HCS1
            have r6 : (S1.resume L' si).L = L' := rfl
            have r7 : (S1.resume L' si).ansd = S1.ansd := rfl
            have r8 : (S1.resume L' si).regs = S1.regs := rfl
            rw [r1, r2, r3, r4, r5, r6, r7, r8]
            iframe
            iframe #
            isplitr
            · ipureintro; simp [Hrcv]
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial
          | ok ei =>
            wp_auto
            wp_apply wp_zapError as %f2 -
            wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f2]
            isplitr
            · ipureintro; rfl
            iintro %fsl ⟨-, -⟩
            wp_auto
            wp_apply wp_Debug V.lg _ _ $$ []
            · iframe #; ipureintro; exact Hlg
            (try wp_auto)
            wp_for_post
            iframe Hrcb
            iexists bo
            simp only [named]
            iframe closeErr cur backoff
            unfold client.runCore
            iexists S1.resume L' si, U, rcv ++ [p], mref, s2, e1
            have r1 : (S1.resume L' si).Dm = S.Dm ++ [m] := HD1
            have r2 : (S1.resume L' si).M = S1.M := rfl
            have r3 : (S1.resume L' si).l = S1.l.dropWhile (fun x => decide (x = null)) := rfl
            have r4 : (S1.resume L' si).CL = S.CL := HCL1
            have r5 : (S1.resume L' si).CS = S.CS := HCS1
            have r6 : (S1.resume L' si).L = L' := rfl
            have r7 : (S1.resume L' si).ansd = S1.ansd := rfl
            have r8 : (S1.resume L' si).regs = S1.regs := rfl
            rw [r1, r2, r3, r4, r5, r6, r7, r8]
            iframe
            iframe #
            isplitr
            · ipureintro; simp [Hrcv]
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial
        | cancel X =>
          obtain ⟨hs0, hev0, hcomp0, hfr0, hcr0, hca0, hid0⟩ : m.src = none ∧ m.evs = [] ∧
              m.compactRev = W64 0 ∧ m.fragment = false ∧ m.created = false ∧ m.canceled = true ∧
              m.watchId = X := by
            simp only [v3rpc.ctrlAnswers] at Hcans; exact Hcans
          rw [hcr0]
          wp_auto
          rw [hca0, hcomp0, hid0]
          wp_auto
          wp_apply wp_mapDelete $$ Hcsm as Hcsm
          wp_apply wp_map_lookup2 $$ Hm as Hm
          icases client.sendTok_lookup γs S.L i (.cancel X) $$ [Hstok Hup] with ⟨Hstok, %HLi⟩
          · iframe; iframe #
          ihave Hfr : iprop(⌜i ∉ S.ansd⌝ ∗ ([∗list] j ∈ S.ansd, client.ansH γs j) ∗ v3rpc.ansTok γa i)
            $$ [Hans Hat]
          · iapply client.ans_fresh
            iframe
            iframe #
          icases Hfr with ⟨%Hia, Hans, Hat⟩
          obtain ⟨Hg2, Hold, Hnew⟩ := client.cancelAns_ok (U := U) (fw := S.M !! X) HgOk HLi Hia
            hs0 hcr0 hid0 rfl
          cases hMX : S.M !! X with
          | none =>
            rw [hMX] at Hg2 Hold
            simp only [hMX, Option.isSome_none, Bool.false_eq_true, decide_false]
            wp_auto
            ihave Hels := BigSepM.bigSepM_impl
                (Ψ := fun ws (_ : Unit) => client.wsElem V γs (S.cancelAns m i X none) ws) $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              have Hws'' : U !! ws' = some u := Hws'
              cases u
              iapply (client.wsElem_mono' V γs (S := S) (S' := S.cancelAns m i X none) ws'
                (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                (fun ph h => Hold ws' ph Hws'' (by simp) h) rfl) $$ Hw'
            wp_for_post
            iframe Hrcb
            iexists bo
            simp only [named]
            iframe closeErr cur backoff
            unfold client.runCore
            iexists S.cancelAns m i X none, U, rcv ++ [p], mref, s, e
            have e1 : (S.cancelAns m i X none).Dm = S.Dm ++ [m] := rfl
            have e2 : (S.cancelAns m i X none).L = S.L := rfl
            have e3 : (S.cancelAns m i X none).ansd = S.ansd ++ [i] := rfl
            have e4 : (S.cancelAns m i X none).regs = S.regs := rfl
            have e5 : (S.cancelAns m i X none).CS = GMap.delete X S.CS := rfl
            have e6 : (S.cancelAns m i X none).M = S.M := rfl
            have e7 : (S.cancelAns m i X none).CL = S.CL := rfl
            have e8 : (S.cancelAns m i X none).l = S.l := rfl
            rw [e1, e2, e3, e4, e5, e6, e7, e8]
            iframe
            iframe #
            isplitr
            · ipureintro; simp [Hrcv]
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            isplitl [Hat]
            · iapply BigSepL.bigSepL_singleton.2
              unfold client.ansH
              iexists γo, γa
              iframe #; iframe
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial
          | some wsx =>
            rw [hMX] at Hg2 Hold Hnew
            have hUx : U !! wsx = some () := HgOk.1 X wsx hMX
            icases (BigSepM.bigSepM_delete hUx).1 $$ Hels with ⟨Hx, Hels⟩
            iunfold client.wsElem at Hx
            icases Hx with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
            subst HPws
            have hreg : ph = .reg X := by
              cases ph with
              | queued si => exact absurd hMX (Hph.1 X)
              | orphan => exact absurd hMX (Hph.1 X)
              | closedRun Y => exact absurd hMX (Hph.1.2.1 X)
              | reg Y =>
                have hY : Y = X := HgOk.2.1 Y X P.ws Hph.1 hMX
                rw [hY]
            subst hreg
            have Hph2 := Hnew P.ws (.reg X) rfl Hph
            simp only [client.wsRest, client.noCancelOk]
            icases Hrest with ⟨%w, %rg, %fcs, %lo, %sent, %C, -, Hprod, -, -⟩
            ihave #HP' := HP
            iunfold wsIs at HP'
            icases HP' with ⟨-, -, #Frecvc, -, -, #Hrecvc, -⟩
            simp only [hMX, Option.isSome_some, _root_.decide_true, Option.getD_some]
            wp_auto
            wp_apply wp_spsc_close P.γr P.recvc (client.recvElem V P) (fun _ => iprop(True)) sent
              $$ [Hprod]
            · iframe Hrecvc Hprod
            wp_pures
            wp_apply wp_mapInsert $$ Hclm as Hclm
            wp_apply wp_mapDelete $$ Hm as Hm
            ihave Hels := BigSepM.bigSepM_impl
                (Ψ := fun ws (_ : Unit) => client.wsElem V γs (S.cancelAns m i X (some P.ws)) ws)
                $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
              have hne : ws' ≠ P.ws := by
                intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
              rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
              cases u
              iapply (client.wsElem_mono' V γs (S := S) (S' := S.cancelAns m i X (some P.ws)) ws'
                (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                (fun ph h => Hold ws' ph Hws'' (fun e => hne (Option.some.inj e).symm) h) rfl) $$ Hw'
            ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                client.wsElem V γs (S.cancelAns m i X (some P.ws)) ws) (m := U) (i := P.ws) (x := ())
                hUx).2 $$ [Hels Hid]
            · iframe Hels
              unfold client.wsElem
              iexists P, .closedRun X
              isplitr
              · ipureintro; exact ⟨rfl, Hph2⟩
              iframe HP
              simp only [WPh.id, client.wsRest, client.noCancelOk]
              iframe Hid
              try itrivial
            wp_for_post
            iframe Hrcb
            iexists bo
            simp only [named]
            iframe closeErr cur backoff
            unfold client.runCore
            iexists S.cancelAns m i X (some P.ws), U, rcv ++ [p], mref, s, e
            have e1 : (S.cancelAns m i X (some P.ws)).Dm = S.Dm ++ [m] := rfl
            have e2 : (S.cancelAns m i X (some P.ws)).L = S.L := rfl
            have e3 : (S.cancelAns m i X (some P.ws)).ansd = S.ansd ++ [i] := rfl
            have e4 : (S.cancelAns m i X (some P.ws)).regs = S.regs := rfl
            have e5 : (S.cancelAns m i X (some P.ws)).CS = GMap.delete X S.CS := rfl
            have e6 : (S.cancelAns m i X (some P.ws)).M = GMap.delete X S.M := rfl
            have e7 : (S.cancelAns m i X (some P.ws)).CL = GMap.insert P.ws () S.CL := rfl
            have e8 : (S.cancelAns m i X (some P.ws)).l = S.l := rfl
            rw [e1, e2, e3, e4, e5, e6, e7, e8]
            iframe
            iframe #
            isplitr
            · ipureintro; simp [Hrcv]
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            isplitl [Hat]
            · iapply BigSepL.bigSepL_singleton.2
              unfold client.ansH
              iexists γo, γa
              iframe #; iframe
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial

        | progress => exact absurd Hcans (by simp [v3rpc.ctrlAnswers])
        | other => exact absurd Hcans (by simp [v3rpc.ctrlAnswers])
      ihave #Hmvcc' := Hmvcc
      iunfold v3rpc.mvccOk at Hmvcc'
      icases Hmvcc' with ⟨%ρ, %rs, %Lp, %Hpure, #HLp, #Hrecv, %Hfilt, -, #Hcov, %Hfr2⟩
      obtain ⟨Hmeq, Hrev, HLplen, Hlast, Hlive⟩ := Hpure
      have hsrc : m.src = some ρ := by rw [Hmeq]; rfl
      have hcr0 : m.created = false := by rw [Hmeq]; rfl
      have hca0 : m.canceled = false := by rw [Hmeq]; rfl
      have hcomp0 : m.compactRev = W64 0 := by rw [Hmeq]; rfl
      have hfr0 : m.fragment = false := by rw [Hmeq]; rfl
      have hid0 : m.watchId = ρ.id := by rw [Hmeq]; rfl
      have hev0 : m.evs = ρ.evs := by rw [Hmeq]; rfl
      iunfold v3rpc.downLbW at HLp
      ihave %Hcmp2 := mono_list_lb_valid _ _ _ $$ HDlb HLp
      have HLpe : Lp = S.Dm := by
        rcases Hcmp2 with h | h
        · exact (List.prefix_iff_eq_take.1 h).trans (List.take_of_length_le (by omega)) |>.symm
        · exact (List.prefix_iff_eq_take.1 h).trans (List.take_of_length_le (by omega))
      subst HLpe
      rw [hcr0]
      wp_auto
      rw [hca0]
      wp_auto
      rw [hfr0]
      wp_auto
      -- what the dispatch reads
      ihave #Hrok : mvcc.respOk ρ $$ []
      · iunfold mvcc.watchRecvOk at Hrecv
        icases Hrecv with ⟨%γw, %rr, %fcs, %Lr, %D, %d, -, -, -, -, -, -, -, #Hrs⟩
        iapply Hrs $$ %ρ %(List.mem_of_getLast? Hlast)
      ihave ⟨%kvs, %Hkvl, #Hea, #Hkv⟩ := client.evs_eventsAt sl ps ρ.evs (by rw [← hev0]; exact Hpslen)
        $$ [Hps Hevs]
      · iframe #; rw [← hev0]; iframe #
      iunfold v3rpc.hdrOwn at Hho
      icases Hho with ⟨%Hhn, Hh1, Hh2, Hhrev, Hh4, Hh5⟩
      ihave Hrf : iprop(respFields p (DFrac.own 1) m h sl) $$ [Hhdr Hwid Hcr Hca Hcomp Hcrs Hfr Hev]
      · unfold respFields
        rw [hcr0, hca0, hcomp0, hfr0, hid0]
        iframe
        ipureintro; exact Hhn
      by_cases hid : ρ.id = W64 (-1)
      · -- a progress response of id `-1` (unit W-K): broadcast to every registered substream
        iunfold v3rpc.mvccCov at Hcov
        icases Hcov with ⟨%γc, %pre, %γo, %γa, #Hax, %Hγ, #Hfwd, #Hsl0, #Hrc, #Hra, #Hcq⟩
        iunfold mvcc.respCov at Hrc
        icases Hrc with ⟨-, #Hcmp, -⟩
        ihave #Hcmp0 := Hcmp
        iunfold mvcc.respCompl at Hcmp
        icases Hcmp with (%hne | ⟨-, %Hr1⟩)
        · exact absurd hid hne
        obtain ⟨hr1, hevn⟩ := Hr1
        have hb : client.isBroadcast m := by
          refine ⟨by rw [hev0, hevn], hca0, hcr0, hcomp0, ?_, by rw [hid0, hid]⟩
          rw [Hrev]; intro h0; rw [h0] at hr1; exact absurd hr1 (by decide)
        have hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y := HgOk.2.1
        have hU : ∀ X ws, S.M !! X = some ws → U !! ws = some () := HgOk.1
        obtain ⟨Hg1, Hph1⟩ := client.recvMvcc_ok HgOk hsrc (fun hne => absurd hid hne)
        ipersist Hhrev
        ihave #Hha : hdrAt h m.hdr.revision $$ []
        · unfold hdrAt; iright; iframe Hhrev; ipureintro; exact Hhn
        have hkv0 : List.zipWith client.evModelOf ρ.evs kvs = [] := by rw [hevn]; rfl
        irevert Hea; rw [hkv0]; iintro #Hea
        -- the registered substreams (`substreams`'s) and the others
        icases client.bigSepM_split_inj (fun ws => client.wsElem V γs S ws) U S.M hU hinj $$ Hels
          with ⟨HelM, HelR⟩
        -- (K2e-7d) the broadcast covers every registered substream's watcher, unless it stopped
        imod client.bcast_covAll V γs ρ γc pre γo γa hinj Hγ.1 Hγ.2.1 Hγ.2.2.1 Hfr2.1 hid
          $$ [Hax Hsl0 Hra Hcmp0 Hcq Hlc3 Hstok HelM] with ⟨Hstok, HelM, #Hcall⟩
        · iframe Hlc3 Hstok HelM; iframe #
        ihave #HDw : v3rpc.downLbW γs S.Dm $$ []
        · unfold v3rpc.downLbW; iexact HDlb
        ihave HelR := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => iprop(⌜∃ X, S.M !! X = some ws⌝ ∨
              client.wsElem V γs (S.recvMvcc m) ws)) $$ HelR []
        · iintro !> %ws' %u %Hws' Hw'
          icases Hw' with (%Hin | Hw')
          · ileft; ipureintro; exact Hin
          iright
          iapply (client.wsElem_recv_other V γs (S := S) (S' := S.recvMvcc m) ws' m ρ hsrc rfl
            (fun X h e => by rw [hid] at e; exact h.2.2.2.2.1 e.symm)
            (fun ph h => Hph1 ws' ph h) rfl) $$ [Hw']
          iframe; iframe #
        ihave HelM := BigSepM.bigSepM_impl
            (Ψ := fun (_X : w64) ws => iprop(|==> ∃ a : client.WsPrm GF × List Loc,
              ⌜a.1.ws = ws⌝ ∗ client.sendCap V a.1 a.2 (fun wr => iprop(wr ↦□ client.wrOf m h sl)) ∗
              (∀ wr : Loc, (client.sendDone a.1 a.2 wr ∨ client.sendFail V a.1 a.2 wr) -∗
                client.wsElem V γs (S.recvMvcc m) ws))) $$ HelM []
        · iintro !> %X %ws' %HX Hw'
          iapply (client.bcast_elem V γs (S := S) (S' := S.recvMvcc m) X ws' rcv.length m ρ h sl hsrc
            hevn ⟨hcomp0, hca0, hcr0⟩ Hhn HX hinj rfl (fun ph h => Hph1 ws' ph h) rfl Hrcv.symm hid
            Hpre.1)
          iframe Hha Hea Hw' Hmvcc HDw Hsmall
          iapply Hcall $$ %X %ws' %HX
        imod (BigSepM.bigSepM_bupd _) $$ HelM with HelM
        icases client.bigSepM_choice_inj (client.dummyWsPrm G γr, ([] : List Loc))
            (fun ws a => iprop(⌜a.1.ws = ws⌝ ∗
              client.sendCap V a.1 a.2 (fun wr => iprop(wr ↦□ client.wrOf m h sl)) ∗
              (∀ wr : Loc, (client.sendDone a.1 a.2 wr ∨ client.sendFail V a.1 a.2 wr) -∗
                client.wsElem V γs (S.recvMvcc m) ws))) S.M hinj $$ HelM with ⟨%f, HelM⟩
        ihave HelM : iprop([∗map] _X ↦ ws ∈ S.M, iprop((⌜(f ws).1.ws = ws⌝ ∗
              client.sendCap V (f ws).1 (f ws).2 (fun wr => iprop(wr ↦□ client.wrOf m h sl))) ∗
              (∀ wr : Loc, (client.sendDone (f ws).1 (f ws).2 wr ∨
                client.sendFail V (f ws).1 (f ws).2 wr) -∗ client.wsElem V γs (S.recvMvcc m) ws)))
            $$ [HelM]
        · iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by
            iintro ⟨Hp, Hc, Hw⟩
            isplitl [Hp Hc]
            · iframe Hp Hc
            iexact Hw)) $$ HelM
        rw [BigSepM.bigSepM_sep_eq]
        icases HelM with ⟨HcapM, HwM⟩
        ihave Hhw : iprop(⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision) $$ []
        · iintro %-; iexact Hha
        wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl [] mref S.M (DFrac.own 1) (DFrac.own 1)
          (fun ws => (f ws).1) (fun ws => (f ws).2)
          $$ [Hrf Hhw Hsub Hm HcapM] as %b ⟨Hrf, Hsub, Hm, Hpost⟩
        · rw [if_pos (decide_eq_true hb)]
          iframe
          iframe #
          ipureintro; rw [hev0, hevn]; rfl
        irevert Hpost
        rw [if_pos (decide_eq_true hb)]
        iintro ⟨%Hbt, %wr, Hpost⟩
        subst Hbt
        ihave HelM : iprop([∗map] _X ↦ ws ∈ S.M, client.wsElem V γs (S.recvMvcc m) ws) $$ [Hpost HwM]
        · iapply BigSepM.bigSepM_wand $$ Hpost
          iapply BigSepM.bigSepM_impl $$ HwM
          iintro !> %X %ws' %HX Hw' Hs
          iapply Hw' $$ %wr Hs
        ihave Hels := client.bigSepM_join_inj (fun ws => client.wsElem V γs (S.recvMvcc m) ws) U S.M
          hU hinj $$ [HelM HelR]
        · iframe
        iunfold respFields at Hrf
        icases Hrf with ⟨%Hhn', Hhdr, Hwid, Hcr, Hca, Hcomp, Hcrs, Hfr, Hev⟩
        wp_auto
        wp_for_post
        iframe Hrcb
        iexists bo
        simp only [named]
        iframe closeErr cur backoff
        unfold client.runCore
        iexists S.recvMvcc m, U, rcv ++ [p], mref, s, e
        have r0 : (S.recvMvcc m).Dm = S.Dm ++ [m] := rfl
        have r1 : (S.recvMvcc m).ansd = S.ansd := rfl
        have r2 : (S.recvMvcc m).regs = S.regs := rfl
        have r3 : (S.recvMvcc m).M = S.M := rfl
        have r4 : (S.recvMvcc m).CL = S.CL := rfl
        have r5 : (S.recvMvcc m).l = S.l := rfl
        have r6 : (S.recvMvcc m).L = S.L := rfl
        have r7 : (S.recvMvcc m).CS = S.CS := rfl
        rw [r0, r1, r2, r3, r4, r5, r6, r7]
        iframe
        iframe #
        isplitr
        · ipureintro; simp [Hrcv]
        isplitl []
        · unfold v3rpc.downLbW; iexact HLlb
        isplitr
        · ipureintro; exact Hg1
        imodintro
        iapply BigSepL.bigSepL_singleton.2
        unfold client.respInfo; rw [hsrc]; iexact Hrok
      have hlive : v3rpc.idLive S.Dm ρ.id := Hlive hid
      cases hMX : S.M !! ρ.id with
      | none =>
        have hnb : ¬ client.isBroadcast m := fun h => by
          obtain ⟨-, -, -, -, -, hw⟩ := h; rw [hid0] at hw; exact hid hw
        ihave Hhw : iprop(|==> (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision)) $$ [Hhrev]
        · by_cases hne : m.evs = []
          · ipersist Hhrev
            imodintro
            iintro %-
            unfold hdrAt; iright
            iframe Hhrev
            ipureintro; exact Hhn
          · imodintro; iintro %he; exact absurd he hne
        imod Hhw
        wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl (List.zipWith client.evModelOf ρ.evs kvs)
          mref S.M (DFrac.own 1) (DFrac.own 1) (fun _ => client.dummyWsPrm G γr) (fun _ => [])
          $$ [Hrf Hhw Hsub Hm] as %b ⟨Hrf, Hsub, Hm, Hpost⟩
        · iframe
          iframe #
          isplitr
          · ipureintro; simp [Hkvl, hev0]
          rw [if_neg (by simpa using hnb), hid0, hMX]
          itrivial
        irevert Hpost
        rw [if_neg (by simpa using hnb), hid0, hMX]
        iintro %Hb
        subst Hb
        wp_auto
        iunfold respFields at Hrf
        icases Hrf with ⟨%Hhn', Hhdr, Hwid, Hcr, Hca, Hcomp, Hcrs, Hfr, Hev⟩
        wp_auto
        wp_apply wp_map_lookup2 $$ Hcsm as Hcsm
        rw [hid0]
        have hXr : ρ.id ∈ S.regs := by
          obtain ⟨mc, hmc, hs, hw, hc, hca⟩ := client.idLive_exists hlive
          rw [← hw]; exact HgOk.2.2.2.2.2.2.2.2.2.2.2.2 mc hmc hs hc hca
        obtain ⟨Hg1, Hph1⟩ := client.recvMvcc_ok HgOk hsrc (fun _ => hlive)
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => client.wsElem V γs (S.recvMvcc m) ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          iapply (client.wsElem_recv_other V γs (S := S) (S' := S.recvMvcc m) ws' m ρ hsrc rfl
            (fun X h e => by subst e; have h1 := h.1; rw [hMX] at h1; cases h1)
            (fun ph h => Hph1 ws' ph h) rfl) $$ [Hw']
          iframe; iframe #
        cases hCS : S.CS !! ρ.id with
        | some u =>
          simp only [Option.isSome_some, _root_.decide_true]
          wp_auto
          wp_for_post
          iframe Hrcb
          iexists bo
          simp only [named]
          iframe closeErr cur backoff
          unfold client.runCore
          iexists S.recvMvcc m, U, rcv ++ [p], mref, s, e
          have r0 : (S.recvMvcc m).Dm = S.Dm ++ [m] := rfl
          have r1 : (S.recvMvcc m).ansd = S.ansd := rfl
          have r2 : (S.recvMvcc m).regs = S.regs := rfl
          have r3 : (S.recvMvcc m).M = S.M := rfl
          have r4 : (S.recvMvcc m).CL = S.CL := rfl
          have r5 : (S.recvMvcc m).l = S.l := rfl
          have r6 : (S.recvMvcc m).L = S.L := rfl
          have r7 : (S.recvMvcc m).CS = S.CS := rfl
          rw [r0, r1, r2, r3, r4, r5, r6, r7]
          iframe
          iframe #
          isplitr
          · ipureintro; simp [Hrcv]
          isplitl []
          · unfold v3rpc.downLbW; iexact HLlb
          isplitr
          · ipureintro; exact Hg1
          imodintro
          iapply BigSepL.bigSepL_singleton.2
          unfold client.respInfo; rw [hsrc]; iexact Hrok
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
          wp_auto
          wp_apply wp_mapInsert $$ Hcsm as Hcsm
          rename_i crp
          irename : (crp ↦ (_ : etcdserverpb.WatchRequest_CancelRequest) : IProp GF) => Hcr'
          imod client.cancelReq_send «$v0_ptr» crp «$r0_ptr» ρ.id
            $$ [«$v0» Hcr' «$r0»] with Hsend
          · iframe
          wp_apply wp_zapInt64 as %f1 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          wp_auto
          wp_apply wp_Debug V.lg _ _ $$ []
          · iframe #; ipureintro; exact Hlg
          wp_apply HSend $$ %S.L %«$r0_ptr» %(.cancel ρ.id) [Hstok Hsend] as %err ⟨-, Hres'⟩
          · iframe
            unfold v3rpc.watchUp v3rpc.watchReqOk
            isplitr <;> itrivial
          ihave ⟨%L', %HL', Hstok⟩ : iprop(∃ L' : List v3rpc.WatchReqM,
              ⌜L' = S.L ∨ L' = S.L ++ [.cancel ρ.id]⌝ ∗ cliSendTok (Req := v3rpc.pbWatchRequest) γs L')
              $$ [Hres']
          · icases Hres' with (⟨-, Htok⟩ | ⟨-, %L', %HL', Htok⟩)
            · iexists _; iframe; ipureintro; right; rfl
            · iexists L'; iframe; ipureintro; exact HL'
          cases err with
          | nil =>
            wp_auto
            wp_for_post
            iframe Hrcb
            iexists bo
            simp only [named]
            iframe closeErr cur backoff
            obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.recvMvcc m) (U := U) Hg1 hXr HL'
            ihave Hels := BigSepM.bigSepM_impl
                (Ψ := fun ws (_ : Unit) => client.wsElem V γs ((S.recvMvcc m).sentCancel ρ.id L') ws) $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              iapply (client.wsElem_mono V γs (S := S.recvMvcc m) (S' := (S.recvMvcc m).sentCancel ρ.id L') ws' rfl
                (fun ph' h => Hph2 ws' ph' h
                  (fun X' e => by
                    subst e; intro eX; subst eX
                    apply h.2.2.2.2.2.1
                    simp only [client.RunSt.recvMvcc]
                    rw [client.idLive_snoc, if_neg (fun hc => by rw [hsrc] at hc; cases hc.1)]
                    exact hlive)
                  (fun e => by subst e; have h1 : S.M !! ρ.id = some ws' := h.1; rw [hMX] at h1; cases h1))
                (fun X hph => client.cancels_of_snoc (.cancel ρ.id) X (fun e => by
                  cases e; have h1 : S.M !! ρ.id = some ws' := hph.1; rw [hMX] at h1; cases h1) HL')) $$ Hw'
            unfold client.runCore
            iexists (S.recvMvcc m).sentCancel ρ.id L', U, rcv ++ [p], mref, s, e
            have r0 : ((S.recvMvcc m).sentCancel ρ.id L').Dm = S.Dm ++ [m] := rfl
            have r1 : ((S.recvMvcc m).sentCancel ρ.id L').ansd = S.ansd := rfl
            have r2 : ((S.recvMvcc m).sentCancel ρ.id L').regs = S.regs := rfl
            have r3 : ((S.recvMvcc m).sentCancel ρ.id L').M = S.M := rfl
            have r4 : ((S.recvMvcc m).sentCancel ρ.id L').CL = S.CL := rfl
            have r5 : ((S.recvMvcc m).sentCancel ρ.id L').l = S.l := rfl
            have r6 : ((S.recvMvcc m).sentCancel ρ.id L').L = L' := rfl
            have r7 : ((S.recvMvcc m).sentCancel ρ.id L').CS = GMap.insert ρ.id () S.CS := rfl
            rw [r0, r1, r2, r3, r4, r5, r6, r7]
            iframe
            iframe #
            isplitr
            · ipureintro; simp [Hrcv]
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hsrc]; iexact Hrok
          | ok ei =>
            wp_auto
            wp_apply wp_zapInt64 as %f1 -
            wp_apply wp_zapError as %f2 -
            wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
            isplitr
            · ipureintro; rfl
            iintro %fsl ⟨-, -⟩
            wp_auto
            wp_apply wp_Debug V.lg _ _ $$ []
            · iframe #; ipureintro; exact Hlg
            wp_for_post
            iframe Hrcb
            iexists bo
            simp only [named]
            iframe closeErr cur backoff
            obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.recvMvcc m) (U := U) Hg1 hXr HL'
            ihave Hels := BigSepM.bigSepM_impl
                (Ψ := fun ws (_ : Unit) => client.wsElem V γs ((S.recvMvcc m).sentCancel ρ.id L') ws) $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              iapply (client.wsElem_mono V γs (S := S.recvMvcc m) (S' := (S.recvMvcc m).sentCancel ρ.id L') ws' rfl
                (fun ph' h => Hph2 ws' ph' h
                  (fun X' e => by
                    subst e; intro eX; subst eX
                    apply h.2.2.2.2.2.1
                    simp only [client.RunSt.recvMvcc]
                    rw [client.idLive_snoc, if_neg (fun hc => by rw [hsrc] at hc; cases hc.1)]
                    exact hlive)
                  (fun e => by subst e; have h1 : S.M !! ρ.id = some ws' := h.1; rw [hMX] at h1; cases h1))
                (fun X hph => client.cancels_of_snoc (.cancel ρ.id) X (fun e => by
                  cases e; have h1 : S.M !! ρ.id = some ws' := hph.1; rw [hMX] at h1; cases h1) HL')) $$ Hw'
            unfold client.runCore
            iexists (S.recvMvcc m).sentCancel ρ.id L', U, rcv ++ [p], mref, s, e
            have r0 : ((S.recvMvcc m).sentCancel ρ.id L').Dm = S.Dm ++ [m] := rfl
            have r1 : ((S.recvMvcc m).sentCancel ρ.id L').ansd = S.ansd := rfl
            have r2 : ((S.recvMvcc m).sentCancel ρ.id L').regs = S.regs := rfl
            have r3 : ((S.recvMvcc m).sentCancel ρ.id L').M = S.M := rfl
            have r4 : ((S.recvMvcc m).sentCancel ρ.id L').CL = S.CL := rfl
            have r5 : ((S.recvMvcc m).sentCancel ρ.id L').l = S.l := rfl
            have r6 : ((S.recvMvcc m).sentCancel ρ.id L').L = L' := rfl
            have r7 : ((S.recvMvcc m).sentCancel ρ.id L').CS = GMap.insert ρ.id () S.CS := rfl
            rw [r0, r1, r2, r3, r4, r5, r6, r7]
            iframe
            iframe #
            isplitr
            · ipureintro; simp [Hrcv]
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hsrc]; iexact Hrok
      | some wsx =>
        have hnb : ¬ client.isBroadcast m := fun h => by
          obtain ⟨-, -, -, -, -, hw⟩ := h; rw [hid0] at hw; exact hid hw
        have hU : U !! wsx = some () := HgOk.1 ρ.id wsx hMX
        icases (BigSepM.bigSepM_delete hU).1 $$ Hels with ⟨Hw, Hels⟩
        iunfold client.wsElem at Hw
        icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
        subst HPws
        have hlive' : v3rpc.idLive (S.Dm ++ [m]) ρ.id := by
          rw [client.idLive_snoc, if_neg (fun h => by rw [hsrc] at h; cases h.1)]; exact hlive
        -- its phase: registered under the response's id
        have hph : ph = WPh.reg ρ.id := by
          cases ph with
          | queued si => exact absurd hMX (Hph.1 ρ.id)
          | orphan => exact absurd hMX (Hph.1 ρ.id)
          | closedRun X => exact absurd hMX (Hph.1.2.1 ρ.id)
          | reg X =>
            have hX : X = ρ.id := HgOk.2.1 X ρ.id P.ws Hph.1 hMX
            rw [hX]
        subst hph
        iunfold client.wsRest at Hrest
        icases Hrest with ⟨%w, %rg, %fcs, %lo, %sent, %C, #Hrg, Hprod, Hauth, Hst, Hc2⟩
        ihave #HP' := HP
        iunfold wsIs at HP'
        icases HP' with ⟨-, -, -, -, -, -, -, -, -, %HPpure, #Hso⟩
        ihave #HDw : v3rpc.downLbW γs S.Dm $$ []
        · unfold v3rpc.downLbW; iexact HDlb
        ihave #Hevs' : iprop([∗list] x ∈ ps.zip ρ.evs, mvcc.evIs x.1 x.2) $$ []
        · rw [← hev0]; iexact Hevs
        ihave Hpre := client.reg_pre V γs P S.Dm rcv.length m ρ rs w rg fcs lo sent C h sl ps kvs
            hsrc hev0 ⟨hcomp0, hca0, hcr0⟩ Hfilt (by rw [← hev0]; exact Hpslen) Hkvl HPpure.2.1 Hpre.2
            Hpre.1 Hhn Hrcv.symm HPpure.2.2 hlive hid $$ [Hauth Hst Hhrev Hc2]
        · iframe; iframe #
        imod Hpre with ⟨%es, %C', %C2, #Hes, %Hesl, Hhw, Hauth, Hcap, Hst, Hpend⟩
        wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl es mref S.M (DFrac.own 1) (DFrac.own 1)
          (fun _ => P) (fun _ => sent)
          $$ [Hrf Hhw Hsub Hm Hprod Hcap] as %b ⟨Hrf, Hsub, Hm, Hpost⟩
        · iframe
          iframe #
          isplitr
          · ipureintro; exact Hesl
          rw [if_neg (by simpa using hnb), hid0, hMX]
          isplitr
          · ipureintro; rfl
          unfold sendCap
          iframe
          iframe #
        irevert Hpost
        rw [if_neg (by simpa using hnb), hid0, hMX]
        iintro ⟨%wr, Hpost⟩
        icases client.post_gx V P sent wr b $$ Hpost with ⟨Hpost, #Hxb⟩
        ihave Hrest := client.reg_post V γs P S.Dm m ρ.id w rg fcs lo sent C' C2 b wr
          $$ [Hauth Hst Hpend Hpost]
        · iframe; iframe #
        obtain ⟨Hg1, Hph1⟩ := client.recvMvcc_ok HgOk hsrc (fun _ => hlive)
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => client.wsElem V γs (S.recvMvcc m) ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
          have hne : ws' ≠ P.ws := by
            intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
          iapply (client.wsElem_recv_other V γs (S := S) (S' := S.recvMvcc m) ws' m ρ hsrc rfl
            (fun X h e => by
              subst e; have h1 : S.M !! ρ.id = some ws' := h.1; rw [hMX] at h1
              exact hne (Option.some.inj h1).symm)
            (fun ph h => Hph1 ws' ph h) rfl) $$ [Hw']
          iframe; iframe #
        iunfold respFields at Hrf
        icases Hrf with ⟨%Hhn', Hhdr, Hwid, Hcr, Hca, Hcomp, Hcrs, Hfr, Hev⟩
        cases b with
        | true =>
          ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
              client.wsElem V γs (S.recvMvcc m) ws) (m := U) (i := P.ws) (x := ()) hU).2 $$ [Hels Hid Hrest]
          · iframe Hels
            unfold client.wsElem
            iexists P, .reg ρ.id
            isplitr
            · ipureintro; exact ⟨rfl, Hph1 P.ws _ Hph⟩
            iframe HP
            iframe
            iapply client.noCancelOk_mono (S := S) (S' := S.recvMvcc m) P _ (fun _ _ _ hi => hi) $$ Hnc
          wp_auto
          wp_for_post
          iframe Hrcb
          iexists bo
          simp only [named]
          iframe closeErr cur backoff
          unfold client.runCore
          iexists S.recvMvcc m, U, rcv ++ [p], mref, s, e
          have r0 : (S.recvMvcc m).Dm = S.Dm ++ [m] := rfl
          have r1 : (S.recvMvcc m).ansd = S.ansd := rfl
          have r2 : (S.recvMvcc m).regs = S.regs := rfl
          have r3 : (S.recvMvcc m).M = S.M := rfl
          have r4 : (S.recvMvcc m).CL = S.CL := rfl
          have r5 : (S.recvMvcc m).l = S.l := rfl
          have r6 : (S.recvMvcc m).L = S.L := rfl
          have r7 : (S.recvMvcc m).CS = S.CS := rfl
          rw [r0, r1, r2, r3, r4, r5, r6, r7]
          iframe
          iframe #
          isplitr
          · ipureintro; simp [Hrcv]
          isplitl []
          · unfold v3rpc.downLbW; iexact HLlb
          isplitr
          · ipureintro; exact Hg1
          imodintro
          iapply BigSepL.bigSepL_singleton.2
          unfold client.respInfo; rw [hsrc]; iexact Hrok
        | false =>
          -- the dispatch failed: the substream stopped (`γx`), so cancelling its id is fine
          icases Hxb with (%hbf | #Hx)
          · cases hbf
          wp_auto
          wp_apply wp_map_lookup2 $$ Hcsm as Hcsm
          rw [hid0]
          have hXr : ρ.id ∈ S.regs := Hph.2.2.2.1
          cases hCS : S.CS !! ρ.id with
          | some u =>
            simp only [Option.isSome_some, _root_.decide_true]
            wp_auto
            wp_for_post
            iframe Hrcb
            iexists bo
            simp only [named]
            iframe closeErr cur backoff
            ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                client.wsElem V γs (S.recvMvcc m) ws) (m := U) (i := P.ws) (x := ()) hU).2
                $$ [Hels Hid Hrest]
            · iframe Hels
              unfold client.wsElem
              iexists P, .reg ρ.id
              isplitr
              · ipureintro; exact ⟨rfl, Hph1 P.ws _ Hph⟩
              iframe HP
              iframe
              unfold client.noCancelOk; iright; iexact Hx
            unfold client.runCore
            iexists S.recvMvcc m, U, rcv ++ [p], mref, s, e
            have r0 : (S.recvMvcc m).Dm = S.Dm ++ [m] := rfl
            have r1 : (S.recvMvcc m).ansd = S.ansd := rfl
            have r2 : (S.recvMvcc m).regs = S.regs := rfl
            have r3 : (S.recvMvcc m).M = S.M := rfl
            have r4 : (S.recvMvcc m).CL = S.CL := rfl
            have r5 : (S.recvMvcc m).l = S.l := rfl
            have r6 : (S.recvMvcc m).L = S.L := rfl
            have r7 : (S.recvMvcc m).CS = S.CS := rfl
            rw [r0, r1, r2, r3, r4, r5, r6, r7]
            iframe
            iframe #
            isplitr
            · ipureintro; simp [Hrcv]
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg1
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hsrc]; iexact Hrok
          | none =>
            simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
            wp_auto
            wp_apply wp_mapInsert $$ Hcsm as Hcsm
            rename_i crp
            irename : (crp ↦ (_ : etcdserverpb.WatchRequest_CancelRequest) : IProp GF) => Hcr'
            imod client.cancelReq_send «$v0_ptr» crp «$r0_ptr» ρ.id
              $$ [«$v0» Hcr' «$r0»] with Hsend
            · iframe
            wp_apply wp_zapInt64 as %f1 -
            wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
            isplitr
            · ipureintro; rfl
            iintro %fsl ⟨-, -⟩
            wp_auto
            wp_apply wp_Debug V.lg _ _ $$ []
            · iframe #; ipureintro; exact Hlg
            wp_apply HSend $$ %S.L %«$r0_ptr» %(.cancel ρ.id) [Hstok Hsend] as %err ⟨-, Hres'⟩
            · iframe
              unfold v3rpc.watchUp v3rpc.watchReqOk
              isplitr <;> itrivial
            ihave ⟨%L', %HL', Hstok⟩ : iprop(∃ L' : List v3rpc.WatchReqM,
                ⌜L' = S.L ∨ L' = S.L ++ [.cancel ρ.id]⌝ ∗ cliSendTok (Req := v3rpc.pbWatchRequest) γs L')
                $$ [Hres']
            · icases Hres' with (⟨-, Htok⟩ | ⟨-, %L', %HL', Htok⟩)
              · iexists _; iframe; ipureintro; right; rfl
              · iexists L'; iframe; ipureintro; exact HL'
            cases err with
            | nil =>
              wp_auto
              wp_for_post
              iframe Hrcb
              iexists bo
              simp only [named]
              iframe closeErr cur backoff
              obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.recvMvcc m) (U := U) Hg1 hXr HL'
              ihave Hels := BigSepM.bigSepM_impl
                  (Ψ := fun ws (_ : Unit) => client.wsElem V γs ((S.recvMvcc m).sentCancel ρ.id L') ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                have hne : ws' ≠ P.ws := by
                  intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                iapply (client.wsElem_mono V γs (S := S.recvMvcc m) (S' := (S.recvMvcc m).sentCancel ρ.id L') ws' rfl
                  (fun ph' h => Hph2 ws' ph' h
                    (fun X' e => by
                      subst e; intro eX; subst eX; exact h.2.2.2.2.2.1 hlive')
                    (fun _ => hCS))
                  (fun X hph => client.cancels_of_snoc (.cancel ρ.id) X (fun e => by
                    cases e
                    have h1 : S.M !! ρ.id = some ws' := hph.1
                    rw [hMX] at h1; cases h1
                    exact absurd rfl hne) HL')) $$ Hw'
              ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                  client.wsElem V γs ((S.recvMvcc m).sentCancel ρ.id L') ws) (m := U) (i := P.ws)
                  (x := ()) hU).2 $$ [Hels Hid Hrest]
              · iframe Hels
                unfold client.wsElem
                iexists P, .reg ρ.id
                isplitr
                · ipureintro
                  exact ⟨rfl, Hph2 P.ws _ (Hph1 P.ws _ Hph) (fun X' e => by cases e) (fun _ => hCS)⟩
                iframe HP
                iframe
                unfold client.noCancelOk; iright; iexact Hx
              unfold client.runCore
              iexists (S.recvMvcc m).sentCancel ρ.id L', U, rcv ++ [p], mref, s, e
              have r0 : ((S.recvMvcc m).sentCancel ρ.id L').Dm = S.Dm ++ [m] := rfl
              have r1 : ((S.recvMvcc m).sentCancel ρ.id L').ansd = S.ansd := rfl
              have r2 : ((S.recvMvcc m).sentCancel ρ.id L').regs = S.regs := rfl
              have r3 : ((S.recvMvcc m).sentCancel ρ.id L').M = S.M := rfl
              have r4 : ((S.recvMvcc m).sentCancel ρ.id L').CL = S.CL := rfl
              have r5 : ((S.recvMvcc m).sentCancel ρ.id L').l = S.l := rfl
              have r6 : ((S.recvMvcc m).sentCancel ρ.id L').L = L' := rfl
              have r7 : ((S.recvMvcc m).sentCancel ρ.id L').CS = GMap.insert ρ.id () S.CS := rfl
              rw [r0, r1, r2, r3, r4, r5, r6, r7]
              iframe
              iframe #
              isplitr
              · ipureintro; simp [Hrcv]
              isplitl []
              · unfold v3rpc.downLbW; iexact HLlb
              isplitr
              · ipureintro; exact Hg2
              imodintro
              iapply BigSepL.bigSepL_singleton.2
              unfold client.respInfo; rw [hsrc]; iexact Hrok
            | ok ei =>
              wp_auto
              wp_apply wp_zapInt64 as %f1 -
              wp_apply wp_zapError as %f2 -
              wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
              isplitr
              · ipureintro; rfl
              iintro %fsl ⟨-, -⟩
              wp_auto
              wp_apply wp_Debug V.lg _ _ $$ []
              · iframe #; ipureintro; exact Hlg
              wp_for_post
              iframe Hrcb
              iexists bo
              simp only [named]
              iframe closeErr cur backoff
              obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.recvMvcc m) (U := U) Hg1 hXr HL'
              ihave Hels := BigSepM.bigSepM_impl
                  (Ψ := fun ws (_ : Unit) => client.wsElem V γs ((S.recvMvcc m).sentCancel ρ.id L') ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                have hne : ws' ≠ P.ws := by
                  intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                iapply (client.wsElem_mono V γs (S := S.recvMvcc m) (S' := (S.recvMvcc m).sentCancel ρ.id L') ws' rfl
                  (fun ph' h => Hph2 ws' ph' h
                    (fun X' e => by
                      subst e; intro eX; subst eX; exact h.2.2.2.2.2.1 hlive')
                    (fun _ => hCS))
                  (fun X hph => client.cancels_of_snoc (.cancel ρ.id) X (fun e => by
                    cases e
                    have h1 : S.M !! ρ.id = some ws' := hph.1
                    rw [hMX] at h1; cases h1
                    exact absurd rfl hne) HL')) $$ Hw'
              ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                  client.wsElem V γs ((S.recvMvcc m).sentCancel ρ.id L') ws) (m := U) (i := P.ws)
                  (x := ()) hU).2 $$ [Hels Hid Hrest]
              · iframe Hels
                unfold client.wsElem
                iexists P, .reg ρ.id
                isplitr
                · ipureintro
                  exact ⟨rfl, Hph2 P.ws _ (Hph1 P.ws _ Hph) (fun X' e => by cases e) (fun _ => hCS)⟩
                iframe HP
                iframe
                unfold client.noCancelOk; iright; iexact Hx
              unfold client.runCore
              iexists (S.recvMvcc m).sentCancel ρ.id L', U, rcv ++ [p], mref, s, e
              have r0 : ((S.recvMvcc m).sentCancel ρ.id L').Dm = S.Dm ++ [m] := rfl
              have r1 : ((S.recvMvcc m).sentCancel ρ.id L').ansd = S.ansd := rfl
              have r2 : ((S.recvMvcc m).sentCancel ρ.id L').regs = S.regs := rfl
              have r3 : ((S.recvMvcc m).sentCancel ρ.id L').M = S.M := rfl
              have r4 : ((S.recvMvcc m).sentCancel ρ.id L').CL = S.CL := rfl
              have r5 : ((S.recvMvcc m).sentCancel ρ.id L').l = S.l := rfl
              have r6 : ((S.recvMvcc m).sentCancel ρ.id L').L = L' := rfl
              have r7 : ((S.recvMvcc m).sentCancel ρ.id L').CS = GMap.insert ρ.id () S.CS := rfl
              rw [r0, r1, r2, r3, r4, r5, r6, r7]
              iframe
              iframe #
              isplitr
              · ipureintro; simp [Hrcv]
              isplitl []
              · unfold v3rpc.downLbW; iexact HLlb
              isplitr
              · ipureintro; exact Hg2
              imodintro
              iapply BigSepL.bigSepL_singleton.2
              unfold client.respInfo; rw [hsrc]; iexact Hrok

    -- errc
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, G.errc, G.γerr
      isplit
      · ipureintro; rfl
      isplit
      · iapply is_bag_is_chan $$ Herrb
      iapply bag_recv_au G.γerr G.errc errP _ $$ [$Hlc1 $Hlc2] Herrb
      inext
      iintro %err Herr
      iunfold errP at Herr
      icases Herr with ⟨%Hen, #Herrk, #Hse⟩
      wp_auto
      wp_apply wp_isHaltErr G.ctx G.cd err $$ [] as %b %Hb
      · iframe #
      cases b
      · iunfold noRetryableStreamErr at HnoRetry
        ihave %Hc := HnoRetry $$ %err Herrk
        exfalso
        rcases Hb rfl with h | h | h
        · exact Hen h
        · exact Hc.1 h
        · exact Hc.2 h
      wp_auto
      wp_for_post
      isplitr
      · ipureintro; rfl
      iapply client.runExit_of_core V G γs γr clm csm closeErr_ptr err
      iframe
      iframe #
    -- ctx.Done
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, dγ
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone
      iintro -
      wp_auto
      wp_for_post
      isplitr
      · ipureintro; rfl
      ihave #Hnil := statusErrOk_nil (GF := GF)
      iapply client.runExit_of_core V G γs γr clm csm closeErr_ptr GoInterface.nil
      iframe
      iframe #
    -- closingc
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, G.closingc,
        G.γclosing
      isplit
      · ipureintro; rfl
      isplit
      · iapply is_bag_is_chan $$ Hclb
      iapply bag_recv_au G.γclosing G.closingc (closingP V G) _ $$ [$Hlc1 $Hlc2] Hclb
      inext
      iintro %wsr Hcp
      iunfold closingP at Hcp
      icases Hcp with ⟨Hbody, Hel⟩
      iunfold client.runCore at Hcore
      icases Hcore with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, Hcsm, Hsub, Hm, Hres, Hs, HcF, #He,
        Hstok, Hrcons, %Hrcv, #HDlb, %HgOk, Hans, Hids, #Hinfo, Hwsa, Hels, Had, Htt, Hdn⟩
      ihave %HU := ghost_map_lookup $$ Hwsa Hel
      icases (BigSepM.bigSepM_delete HU).1 $$ Hels with ⟨Hw, Hels⟩
      iunfold client.wsElem at Hw
      icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc⟩
      imod ghost_map_delete $$ Hwsa Hel with Hwsa
      subst HPws
      obtain ⟨Hg', Hph'⟩ := client.closeWs_ok HgOk HU Hph
      ihave Hels := BigSepM.bigSepM_impl
          (Ψ := fun ws (_ : Unit) => client.wsElem V γs (S.closeWs P.ws ph) ws) $$ Hels []
      · iintro !> %ws' %u %Hws' Hw'
        have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
        have hne : ws' ≠ P.ws := by
          intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
        have hU' : U !! ws' = some () := by
          rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''; exact Hws''
        iapply (client.wsElem_mono V γs (S := S) (S' := S.closeWs P.ws ph) ws' rfl
          (fun ph' h => Hph' ws' ph' hne hU' h) (fun _ _ _ hi => hi)) $$ Hw'
      iunfold sliceOwn at Hs
      icases Hs with ⟨Hs, Hscap⟩
      wp_auto
      wp_apply wp_closeSub V G.wgs P.ws ph.id e (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) mref S.M s S.l
        $$ [Hbody Hid HcF Hsub Hm Hres Hs] as ⟨Hid, HcF, Hsub, Hres, Hrest2⟩
      · iframe; iframe #
      ihave ⟨Hm, Hs⟩ : iprop(ownMap mref (DFrac.own 1) (S.closeWs P.ws ph).M ∗
          s ↦* (S.closeWs P.ws ph).l) $$ [Hrest2]
      · unfold client.RunSt.closeWs
        by_cases hid : ph.id = W64 (-1)
        · irevert Hrest2
          simp only [hid, _root_.decide_true, ↓reduceIte]
          iintro H; iexact H
        · irevert Hrest2
          simp only [hid, decide_false, ↓reduceIte, Bool.false_eq_true]
          iintro H; iexact H
      ihave Hs : iprop(sliceOwn s (S.closeWs P.ws ph).l) $$ [Hs Hscap]
      · unfold sliceOwn; iframe
      wp_apply wp_mapDelete $$ Hclm as Hclm
      wp_apply wp_map_len $$ Hm as Hm
      wp_if_destruct
      · wp_for_post
        isplitr
        · ipureintro; rfl
        ihave #Hnil := statusErrOk_nil (GF := GF)
        iapply client.runExit_of_core V G γs γr clm csm closeErr_ptr GoInterface.nil
        iframe closeErr Hnil
        unfold client.runCore
        iexists S.closeWs P.ws ph, GMap.delete P.ws U, rcv, mref, s, e
        have h1 : (S.closeWs P.ws ph).Dm = S.Dm := rfl
        have h2 : (S.closeWs P.ws ph).L = S.L := rfl
        have h3 : (S.closeWs P.ws ph).ansd = S.ansd := rfl
        have h4 : (S.closeWs P.ws ph).regs = S.regs := rfl
        have h5 : (S.closeWs P.ws ph).CS = S.CS := rfl
        rw [h1, h2, h3, h4, h5]
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hrcv
        ipureintro; exact Hg'
      by_cases hid : ph.id = W64 (-1)
      · simp only [show decide (ph.id = W64 (-1)) = true by simp [hid], Bool.not_true]
        wp_auto
        wp_for_post
        iframe Hrcb
        iexists bo
        simp only [named]
        iframe closeErr cur backoff
        unfold client.runCore
        iexists S.closeWs P.ws ph, GMap.delete P.ws U, rcv, mref, s, e
        have h1 : (S.closeWs P.ws ph).Dm = S.Dm := rfl
        have h2 : (S.closeWs P.ws ph).L = S.L := rfl
        have h3 : (S.closeWs P.ws ph).ansd = S.ansd := rfl
        have h4 : (S.closeWs P.ws ph).regs = S.regs := rfl
        have h5 : (S.closeWs P.ws ph).CS = S.CS := rfl
        rw [h1, h2, h3, h4, h5]
        iframe
        iframe #
        ipureintro; exact ⟨Hrcv, Hg'⟩
      simp only [show decide (ph.id = W64 (-1)) = false by simp [hid], Bool.not_false]
      wp_auto
      wp_apply wp_mapInsert $$ Hcsm as Hcsm
      rename_i crp
      irename : (crp ↦ (_ : etcdserverpb.WatchRequest_CancelRequest) : IProp GF) => Hcr
      imod client.cancelReq_send «$v0_ptr» crp «$r0_ptr» ph.id
        $$ [«$v0» Hcr «$r0»] with Hsend
      · iframe
      wp_apply wp_zapInt64 as %f1 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      wp_auto
      wp_apply wp_Debug V.lg _ _ $$ []
      · iframe #; ipureintro; exact Hlg
      wp_apply HSend $$ %S.L %«$r0_ptr» %(.cancel ph.id) [Hstok Hsend] as %err ⟨-, Hres⟩
      · iframe
        unfold v3rpc.watchUp v3rpc.watchReqOk
        isplitr <;> itrivial
      ihave ⟨%L', %HL', Hstok⟩ : iprop(∃ L' : List v3rpc.WatchReqM,
          ⌜L' = S.L ∨ L' = S.L ++ [.cancel ph.id]⌝ ∗ cliSendTok (Req := v3rpc.pbWatchRequest) γs L')
          $$ [Hres]
      · icases Hres with (⟨-, Htok⟩ | ⟨-, %L', %HL', Htok⟩)
        · iexists _; iframe; ipureintro; right; rfl
        · iexists L'; iframe; ipureintro; exact HL'
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe Hrcb
        iexists bo
        simp only [named]
        iframe closeErr cur backoff
        have hXr : ph.id ∈ S.regs := by
          cases ph with
          | queued si => exact absurd rfl hid
          | reg X => exact Hph.2.2.2.1
          | closedRun X => exact absurd rfl hid
          | orphan => exact absurd rfl hid
        have hM1 : (S.closeWs P.ws ph).M !! ph.id = none := by
          unfold client.RunSt.closeWs; simp only [hid, ↓reduceIte]; exact GMap.lookup_delete _ _
        have hC1 : (S.closeWs P.ws ph).CI !! ph.id = none := by
          have hcid : ph.cid = ph.id := by
            cases ph with
            | reg X => rfl
            | _ => exact absurd rfl hid
          unfold client.RunSt.closeWs; simp only [hcid, hid, ↓reduceIte]; exact GMap.lookup_delete _ _
        obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.closeWs P.ws ph) (U := GMap.delete P.ws U)
          Hg' hXr HL'
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) =>
              client.wsElem V γs ((S.closeWs P.ws ph).sentCancel ph.id L') ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          iapply (client.wsElem_mono V γs (S := S.closeWs P.ws ph)
            (S' := (S.closeWs P.ws ph).sentCancel ph.id L') ws' rfl
            (fun ph' h => Hph2 ws' ph' h
              (fun X' e => by
                subst e; intro eX; subst eX; have h1 := h.1.2.2; rw [hC1] at h1; cases h1)
              (fun e => by subst e; have h1 := h.1; rw [hM1] at h1; cases h1))
            (fun X hph => client.cancels_of_snoc (.cancel ph.id) X (fun e => by
              cases e; have h1 := hph.1; rw [hM1] at h1; cases h1) HL')) $$ Hw'
        unfold client.runCore
        iexists (S.closeWs P.ws ph).sentCancel ph.id L', GMap.delete P.ws U, rcv, mref, s, e
        have e1 : ((S.closeWs P.ws ph).sentCancel ph.id L').M = (S.closeWs P.ws ph).M := rfl
        have e2 : ((S.closeWs P.ws ph).sentCancel ph.id L').l = (S.closeWs P.ws ph).l := rfl
        have e3 : ((S.closeWs P.ws ph).sentCancel ph.id L').CL = (S.closeWs P.ws ph).CL := rfl
        have e4 : ((S.closeWs P.ws ph).sentCancel ph.id L').Dm = S.Dm := rfl
        have e5 : ((S.closeWs P.ws ph).sentCancel ph.id L').L = L' := rfl
        have e6 : ((S.closeWs P.ws ph).sentCancel ph.id L').ansd = S.ansd := rfl
        have e7 : ((S.closeWs P.ws ph).sentCancel ph.id L').regs = S.regs := rfl
        have e8 : ((S.closeWs P.ws ph).sentCancel ph.id L').CS = GMap.insert ph.id () S.CS := rfl
        rw [e1, e2, e3, e4, e5, e6, e7, e8]
        iframe
        iframe #
        ipureintro; exact ⟨Hrcv, Hg2⟩
      | ok ei =>
        wp_auto
        wp_apply wp_zapInt64 as %f1 -
        wp_apply wp_zapError as %f2 -
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        wp_auto
        wp_apply wp_Debug V.lg _ _ $$ []
        · iframe #; ipureintro; exact Hlg
        wp_for_post
        iframe Hrcb
        iexists bo
        simp only [named]
        iframe closeErr cur backoff
        have hXr : ph.id ∈ S.regs := by
          cases ph with
          | queued si => exact absurd rfl hid
          | reg X => exact Hph.2.2.2.1
          | closedRun X => exact absurd rfl hid
          | orphan => exact absurd rfl hid
        have hM1 : (S.closeWs P.ws ph).M !! ph.id = none := by
          unfold client.RunSt.closeWs; simp only [hid, ↓reduceIte]; exact GMap.lookup_delete _ _
        have hC1 : (S.closeWs P.ws ph).CI !! ph.id = none := by
          have hcid : ph.cid = ph.id := by
            cases ph with
            | reg X => rfl
            | _ => exact absurd rfl hid
          unfold client.RunSt.closeWs; simp only [hcid, hid, ↓reduceIte]; exact GMap.lookup_delete _ _
        obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.closeWs P.ws ph) (U := GMap.delete P.ws U)
          Hg' hXr HL'
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) =>
              client.wsElem V γs ((S.closeWs P.ws ph).sentCancel ph.id L') ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          iapply (client.wsElem_mono V γs (S := S.closeWs P.ws ph)
            (S' := (S.closeWs P.ws ph).sentCancel ph.id L') ws' rfl
            (fun ph' h => Hph2 ws' ph' h
              (fun X' e => by
                subst e; intro eX; subst eX; have h1 := h.1.2.2; rw [hC1] at h1; cases h1)
              (fun e => by subst e; have h1 := h.1; rw [hM1] at h1; cases h1))
            (fun X hph => client.cancels_of_snoc (.cancel ph.id) X (fun e => by
              cases e; have h1 := hph.1; rw [hM1] at h1; cases h1) HL')) $$ Hw'
        unfold client.runCore
        iexists (S.closeWs P.ws ph).sentCancel ph.id L', GMap.delete P.ws U, rcv, mref, s, e
        have e1 : ((S.closeWs P.ws ph).sentCancel ph.id L').M = (S.closeWs P.ws ph).M := rfl
        have e2 : ((S.closeWs P.ws ph).sentCancel ph.id L').l = (S.closeWs P.ws ph).l := rfl
        have e3 : ((S.closeWs P.ws ph).sentCancel ph.id L').CL = (S.closeWs P.ws ph).CL := rfl
        have e4 : ((S.closeWs P.ws ph).sentCancel ph.id L').Dm = S.Dm := rfl
        have e5 : ((S.closeWs P.ws ph).sentCancel ph.id L').L = L' := rfl
        have e6 : ((S.closeWs P.ws ph).sentCancel ph.id L').ansd = S.ansd := rfl
        have e7 : ((S.closeWs P.ws ph).sentCancel ph.id L').regs = S.regs := rfl
        have e8 : ((S.closeWs P.ws ph).sentCancel ph.id L').CS = GMap.insert ph.id () S.CS := rfl
        rw [e1, e2, e3, e4, e5, e6, e7, e8]
        iframe
        iframe #
        ipureintro; exact ⟨Hrcv, Hg2⟩
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iintro %v ⟨%Hv, Hexit⟩
  subst Hv
  iunfold client.runExit at Hexit
  icases Hexit with ⟨%γs, %S, %U, %ce, %e, %mref, %s, HcE, #Hce, Hclm, Hsub, Hm, Hres, Hs, HcF, #He,
    %HgOk, Hwsa, Hels, Had, Htt, Hdn⟩
  wp_auto
  ipersist HcF
  ihave ⟨Hids, Hcls, #Hdcs⟩ := client.wsElems_split V γs S U $$ Hels
  -- the substreams' loop: close the `recvc` of each not yet closing
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List w64) (_ : Int) => iprop(∃ (CL' U1 : GMap Loc Unit) (wv : Loc),
      ws_ptr ↦ wv ∗ ownMap clm (DFrac.own 1) CL' ∗ ([∗map] ws ↦ _u ∈ U1, client.closerE V S ws) ∗
      ⌜client.tdOk S U CL' U1⌝)) $$ Hm
  iintro %keys ⟨%Hk1, %Hk2, %Hk3⟩
  isplitl [ws Hclm Hcls]
  · iexists S.CL, U, _
    iframe
    ipureintro; exact client.tdOk_init S U
  isplitr
  · imodintro
    iintro %ik %X %wsv ⟨%HkX, %HMX⟩ ⟨%CL', %U1, %wv, Hwsp, Hclm, Hcls, %Htd⟩
    wp_auto
    wp_apply wp_map_lookup2 $$ Hclm as Hclm
    cases hcl : CL' !! wsv with
    | some u =>
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists CL', U1, wsv
      iframe
      ipureintro; exact Htd
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false, Option.getD_none]
      have hU : U !! wsv = some () := HgOk.1 X wsv HMX
      have hU1 : U1 !! wsv = some () := Htd.2.1 wsv hU hcl
      icases (BigSepM.bigSepM_delete hU1).1 $$ Hcls with ⟨Hc, Hcls⟩
      iunfold client.closerE at Hc
      icases Hc with ⟨%ph, %Hph, Hc⟩
      have hreg : ∃ X', ph = .reg X' := by
        cases ph with
        | queued si => exact absurd HMX (Hph.1 X)
        | reg X' => exact ⟨X', rfl⟩
        | closedRun X' => rw [Htd.2.2 wsv Hph.2.2.1] at hcl; cases hcl
        | orphan => exact absurd HMX (Hph.1 X)
      obtain ⟨X', rfl⟩ := hreg
      iunfold client.closerRes at Hc
      iunfold recvcCloser at Hc
      icases Hc with ⟨%P, %sent, %HPws, #HP, Hprod⟩
      subst HPws
      ihave #HP' := HP
      iunfold wsIs at HP'
      icases HP' with ⟨-, -, #Frecvc, -, -, #Hrecvc, -⟩
      wp_pures
      wp_auto
      wp_apply wp_spsc_close P.γr P.recvc (client.recvElem V P) (fun _ => iprop(True)) sent
        $$ [Hprod]
      · iframe Hrecvc Hprod
      wp_pures
      wp_apply wp_mapInsert $$ Hclm as Hclm
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, P.ws
      iframe
      ipureintro; exact client.tdOk_close Htd P.ws
  iintro ⟨%CL', %U1, %wv, Hwsp, Hclm, Hcls, %Htd⟩ Hm
  iunfold sliceOwn at Hs
  icases Hs with ⟨Hs, Hscap⟩
  ihave %Hslen := ownSlice_len $$ Hs
  wp_auto
  ihave IH2 : iprop(∃ (n : w64) (wv : Loc) (CL' U1 : GMap Loc Unit),
      "i" ∷ i_ptr ↦ n ∗ "ws" ∷ ws_ptr ↦ wv ∗ "Hclm" ∷ ownMap clm (DFrac.own 1) CL' ∗
      "Hcls" ∷ ([∗map] ws ↦ _u ∈ U1, client.closerE V S ws) ∗ "Hs" ∷ s ↦* S.l ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (S.l.length : Int) ∧ client.tdOk S U CL' U1⌝)
      $$ [i ws Hclm Hcls Hs]
  · iexists W64 0, _, CL', U1
    simp only [named]
    iframe
    ipureintro; refine ⟨by word, by word, Htd⟩
  wp_for IH2
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z s.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < S.l.length := by word
    obtain ⟨wsv, Hwsv⟩ : ∃ wsv, S.l[sint.nat n]? = some wsv := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, Hif'⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) wsv s (DFrac.own 1) S.l Hn.1 (by simpa using Hwsv) $$ Hs
      with ⟨Hel, Hs⟩
    wp_auto
    ihave Hs := Hs $$ Hel
    have Hset : S.l.set (sint.Z n).toNat wsv = S.l := by
      apply List.ext_getElem?
      intro j
      rw [List.getElem?_set]
      by_cases hj : (sint.Z n).toNat = j
      · subst hj
        have : (sint.Z n).toNat < S.l.length := by word
        simp only [if_pos rfl, this, ↓reduceIte]
        rw [show (sint.Z n).toNat = sint.nat n by rfl] at *
        exact Hwsv.symm
      · simp [hj]
    rw [Hset]
    wp_apply wp_map_lookup2 $$ Hclm as Hclm
    wp_pures
    by_cases hnull : wsv = null
    · simp only [hnull, _root_.decide_true, Bool.not_true]
      wp_pures
      wp_for_post
      iframe
      iexists _, _, CL', U1
      simp only [named]
      iframe
      ipureintro; refine ⟨by word, by word, Hn.2.2⟩
    simp only [hnull, decide_false, Bool.not_false]
    have hmem : wsv ∈ S.l := List.mem_of_getElem? Hwsv
    cases hcl : CL' !! wsv with
    | some u =>
      simp only [Option.isSome_some, _root_.decide_true, Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, CL', U1
      simp only [named]
      iframe
      ipureintro; refine ⟨by word, by word, Hn.2.2⟩
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      have hU : U !! wsv = some () := HgOk.2.2.1 wsv hmem hnull
      have hU1 : U1 !! wsv = some () := Hn.2.2.2.1 wsv hU hcl
      icases (BigSepM.bigSepM_delete hU1).1 $$ Hcls with ⟨Hc, Hcls⟩
      iunfold client.closerE at Hc
      icases Hc with ⟨%ph, %Hph, Hc⟩
      have hq : ∃ si, ph = .queued si := by
        cases ph with
        | queued si => exact ⟨si, rfl⟩
        | reg X' => exact absurd hmem Hph.2.1
        | closedRun X' => exact absurd hmem Hph.2.1
        | orphan => exact absurd hmem Hph.2.1
      obtain ⟨si, rfl⟩ := hq
      iunfold client.closerRes at Hc
      iunfold recvcCloser at Hc
      icases Hc with ⟨%P, %sent, %HPws, #HP, Hprod⟩
      subst HPws
      ihave #HP' := HP
      iunfold wsIs at HP'
      icases HP' with ⟨-, -, #Frecvc, -, -, #Hrecvc, -⟩
      wp_pures
      wp_auto
      wp_apply wp_spsc_close P.γr P.recvc (client.recvElem V P) (fun _ => iprop(True)) sent
        $$ [Hprod]
      · iframe Hrecvc Hprod
      wp_pures
      wp_apply wp_mapInsert $$ Hclm as Hclm
      wp_pures
      wp_for_post
      iframe
      iexists _, _, _, _
      simp only [named]
      iframe
      ipureintro; refine ⟨by word, by word, client.tdOk_close Hn.2.2 P.ws⟩
  have Hnot : ¬ (sint.Z n < sint.Z s.len) := by
    first | exact Hif | exact (fun h => Hif (by simp [h]))
  (try simp only [Hnot, decide_false])
  (try cleanup_bool_decide)
  (try rw [if_pos (by simp)])
  (try wp_auto)
  -- the loop's end: join, then wait for the closing substreams
  ihave HdM : iprop([∗map] _k ↦ ws ∈ S.M, donecOf ws) $$ []
  · iapply (BigSepM.bigSepM_intro (P := iprop(□ ∀ ws, ⌜U !! ws = some ()⌝ → donecOf (GF := GF) ws))
      (fun {X ws} hX => by iintro #H; iapply H $$ %ws %(HgOk.1 X ws hX))) $$ Hdcs
  ihave HdL : iprop([∗list] ws ∈ S.l, ⌜ws = null⌝ ∨ donecOf ws) $$ []
  · iapply (BigSepL.bigSepL_intro (P := iprop(□ ∀ ws, ⌜U !! ws = some ()⌝ → donecOf (GF := GF) ws))
      (fun {k ws} hk => by
        iintro #H
        by_cases hn : ws = null
        · ileft; ipureintro; exact hn
        · iright
          iapply H $$ %ws %(HgOk.2.2.1 ws (List.mem_of_getElem? hk) hn))) $$ Hdcs
  wp_apply wp_join G.wgs mref S.M s S.l (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
    $$ [Hsub Hm Hres Hs HdM HdL] as ⟨Hsub, Hm, Hres, Hs⟩
  · iframe
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List Loc) (_ : Int) => iprop(∃ (M' : GMap w64 Loc)
      (l' : List Loc) (U' : GMap Loc Unit),
      ownMap mref (DFrac.own 1) M' ∗ s ↦* l' ∗ ghostMapAuth G.γws 1 U' ∗
      ([∗map] ws ↦ _u ∈ U', client.idE ws) ∗ wgsF G.wgs go!"substreams" ↦ mref ∗
      wgsF G.wgs go!"resuming" ↦ s)) $$ Hclm
  iintro %keys ⟨%Hk1, %Hk2, %Hk3⟩
  isplitl [Hm Hs Hwsa Hids Hsub Hres]
  · iexists _, _, _
    iframe
  isplitr
  · imodintro
    iintro %ik %wk %u ⟨%Hkw, %Hu⟩ ⟨%M', %l', %U', Hm, Hs, Hwsa, Hids, Hsub, Hres⟩
    wp_auto
    wp_apply wp_bag_receive G.γclosing G.closingc (closingP V G) $$ Hclb as %wsr Hcp
    iunfold closingP at Hcp
    icases Hcp with ⟨Hbody, Hel⟩
    ihave %HU' := ghost_map_lookup $$ Hwsa Hel
    icases (BigSepM.bigSepM_delete HU').1 $$ Hids with ⟨Hid, Hids⟩
    iunfold client.idE at Hid
    icases Hid with ⟨%idv, Hid⟩
    imod ghost_map_delete $$ Hwsa Hel with Hwsa
    wp_apply wp_closeSub V G.wgs wsr idv ce DFrac.discard (DFrac.own 1) (DFrac.own 1) mref M' s l'
      $$ [Hbody Hid Hsub Hm Hres Hs] as ⟨Hid, -, Hsub, Hres, Hrest⟩
    · iframe; iframe #
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    by_cases hid : idv = W64 (-1)
    · irevert Hrest
      simp only [hid, _root_.decide_true, ↓reduceIte]
      iintro ⟨Hm, Hs⟩
      iexists _, _, _
      iframe
    · irevert Hrest
      simp only [hid, decide_false, ↓reduceIte, Bool.false_eq_true]
      iintro ⟨Hm, Hs⟩
      iexists _, _, _
      iframe
  iintro ⟨%M', %l', %U', Hm, Hs, Hwsa, Hids, Hsub, Hres⟩ Hclm
  wp_auto
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold wgAdder at Had
  wp_apply wp_wgsWg_Wait $$ [Had]
  · iframe
  wp_apply wp_closeStream V G callSl $$ [Hdn]
  · iframe #
    iframe
    unfold closeErrPub
    iexists ce
    iframe #
  iapply HΦ
  iexact Htt

end proof

end EtcdGrove
end Perennial
