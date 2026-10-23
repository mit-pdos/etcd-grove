/-
**`watchGRPCStream.run`'s state** (the watch slice's unit W-C; D25): what `run` knows and holds of
the gRPC watch stream and its substreams (`RunSt`, `wsElem`, `runCore`), and the lemmas its proof
and `newWatchClient`'s (the reconnection) use. Moved out of `watchGRPCStream__run.lean` so that
`newWatchClient`'s spec can state the reconnection over it. Lean-first (no Rocq counterpart).
-/
module

public import Proof.ReceiptTactics
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
public import Proof.go_etcd_io.etcd.client.v3.WatchResumeSrv
public import Proof.go_etcd_io.etcd.client.v3.WatchEpoch

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

/-- The create request of a watch. -/
abbrev createOfP (P : WsPrm GF) : v3rpc.CreateReqM := createOf P.key P.ed P.rev P.pn P.sr

/-- (D25) The create request of a registration's base. -/
abbrev createOfB (P : WsPrm GF) (B : RegB) : v3rpc.CreateReqM := createOf P.key P.ed B.rr P.pn B.srr

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
def regFacts (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF) (B : RegB)
    (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) : IProp GF :=
  iprop(⌜v3rpc.createRangeOk (createOfB P B) X rg⌝ ∗ mvcc.watcherIs V.R.γ w rg fcs lo ∗
    fcs ↦*□ ([] : List GoFunc) ∗
    (∃ γw : mvcc.WatcherNames, mvcc.watcherMeta V.R.γ w γw) ∗ regSnap γs Dm w ∗
    ∃ (γo : mvcc.WsStreamNames) (γa : GName), streamAuxIs γs (v3rpc.auxOf γo γa) ∗
      mvcc.idAssigned γo X w)

instance regFacts_persistent (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (P : WsPrm GF) (B : RegB) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) :
    Persistent (regFacts V γs Dm P B X w rg fcs lo) := by
  unfold regFacts; infer_instance

/-- `regFacts` over more responses. -/
theorem regFacts_mono (V : WEnv GF) (γs : StreamNames) {Dm Dm' : List v3rpc.WatchRespM}
    (P : WsPrm GF) (B : RegB) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
    (hp : Dm <+: Dm') : regFacts V γs Dm P B X w rg fcs lo ⊢ regFacts V γs Dm' P B X w rg fcs lo := by
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
def cursorOk (V : WEnv GF) (P : WsPrm GF) (B : RegB) (Dm : List v3rpc.WatchRespM) (w : Loc)
    (rg : mvcc.WatchRange) (lo : Nat) (hi : w64) : IProp GF :=
  iprop(⌜(evsSoFar Dm w = [] ∧ hi = B.hb) ∨
      (∃ e, (evsSoFar Dm w).getLast? = some e ∧ hi = e.kv.modRev)⌝ ∗
    (⌜evsSoFar Dm w = []⌝ ∨ ∃ (L1 : mvcc.Log) (d1 : Nat), mvcc.idxSealed V.R.γ.st.idx L1 ∗
      ⌜evsSoFar Dm w = mvcc.watchEvents L1 rg lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length⌝))

instance cursorOk_persistent (V : WEnv GF) (P : WsPrm GF) (B : RegB) (Dm : List v3rpc.WatchRespM) (w : Loc)
    (rg : mvcc.WatchRange) (lo : Nat) (hi : w64) : Persistent (cursorOk V P B Dm w rg lo hi) := by
  unfold cursorOk; infer_instance

/-- **The second dispatch cursor of a registered substream** (K2e-7d; `sent` the responses
dispatched): `γh2`'s positions `C2`, and, unless the watch promises no completeness or the
substream stopped, one more than the responses, the last the cursor (`cur2Ok`). -/
def cur2St (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF) (B : RegB)
    (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc) : IProp GF :=
  iprop(∃ C2 : List w64, monoListAuthOwn P.γh2 1 C2 ∗
    (⌜P.γ.cpl = false⌝ ∨ dghostVar P.γx DFrac.discard true ∨
      ⌜C2.length = sent.length + 1⌝ ∗ ∃ c2 : w64, ⌜C2.getLast? = some c2⌝ ∗
        cur2Ok V γs B.rr Dm X w rg lo c2))

/-- `cur2St` over more responses, none of the watcher's events. -/
theorem cur2St_mono (V : WEnv GF) (γs : StreamNames) {Dm Dm' : List v3rpc.WatchRespM}
    (P : WsPrm GF) (B : RegB) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc)
    (h : evsOf Dm' w = evsOf Dm w) (hp : Dm <+: Dm') :
    cur2St V γs Dm P B X w rg lo sent ⊢ cur2St V γs Dm' P B X w rg lo sent := by
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
    iapply cur2Ok_mono V γs B.rr X w rg lo c2 h hp $$ Hc

/-- A create request at the stream's up position `si`, if any (a queued substream's). -/
def upAtOpt (γs : StreamNames) (si : Option Nat) (c : v3rpc.CreateReqM) : IProp GF :=
  match si with
  | some i => v3rpc.upAtW γs i (.create c)
  | none => iprop(True)

instance upAtOpt_persistent (γs : StreamNames) (si : Option Nat) (c : v3rpc.CreateReqM) :
    Persistent (upAtOpt (GF := GF) γs si c) := by
  unfold upAtOpt; split <;> infer_instance

/-- **What `run` holds of a substream in its phase** (but its id field). -/
def wsRest (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF) :
    WPh → IProp GF
  | .queued si => iprop((∃ (B : RegB) (sent : List Loc) (C C2 : List w64),
      ⌜regBOk P B⌝ ∗ startOk V B.srr B.rr ∗ sspscProducer P.γr sent ∗
      monoListAuthOwn P.γhi 1 C ∗ monoListAuthOwn P.γh2 1 C2 ∗
      ⌜C.length = sent.length + 1 ∧ C.getLast? = some B.hb ∧
        (P.γ.cpl = true → C2.length = sent.length + 1 ∧ C2.getLast? = some (B.rr - W64 1))⌝ ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} B.rr ∗ psSt P sent.length ∗
      upAtOpt γs si (createOfB P B)) ∨
    -- (D25) stopped for good when a reconnection resumed it: what its create and registration need
    (dghostVar P.γx DFrac.discard true ∗ ∃ (B : RegB) (sent : List Loc) (C C2 : List w64) (q : Qp),
      ⌜regBOk P B⌝ ∗ startOk V B.srr B.rr ∗ sspscProducer P.γr sent ∗
      monoListAuthOwn P.γhi 1 C ∗ monoListAuthOwn P.γh2 1 C2 ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own q} B.rr ∗ upAtOpt γs si (createOfB P B)))
  | .reg X => iprop(∃ (B : RegB) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
      (sent : List Loc) (C : List w64),
      ⌜regBOk P B⌝ ∗ startOk V B.srr B.rr ∗
      regFacts V γs Dm P B X w rg fcs lo ∗ sspscProducer P.γr sent ∗ monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ (∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P B Dm w rg lo hi) ∗ psAt P sent.length) ∗
      cur2St V γs Dm P B X w rg lo sent)
  | .closedRun _ => dghostVar P.γx DFrac.discard true
  | .closed => dghostVar P.γx DFrac.discard true
  | .orphan => iprop(True)

/-- **A fresh substream's queued state** (its first create, base `regB0`). -/
theorem queued_fresh (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF)
    (si : Option Nat) (hB : regBOk P (regB0 P)) :
    startOk V P.sr P.rev ∗ sspscProducer P.γr ([] : List Loc) ∗
      monoListAuthOwn P.γhi 1 [P.rev - W64 1] ∗ monoListAuthOwn P.γh2 1 [P.rev - W64 1] ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} P.rev ∗ psQ P ∗
      upAtOpt γs si (createOfP P) ⊢
    wsRest V γs Dm P (.queued si) := by
  iintro ⟨#Hso, Hprod, Ha, Ha2, Hrv, Hps, Hup⟩
  simp only [wsRest]
  ileft
  iexists regB0 P, [], [P.rev - W64 1], [P.rev - W64 1]
  iframe Hso Hprod Ha Ha2 Hrv Hup
  isplitr
  · ipureintro; exact hB
  isplitr
  · ipureintro; simp
  iapply psQ_psSt; iexact Hps

/-- **A queued substream's create** (`toPB`, D25: for a resumed or stopped one too): its base's start
read from (a fraction of) the request's `rev` field, and the queued state back with the create sent
at any up position of any stream. -/
theorem queued_send (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF)
    (si : Option Nat) :
    wsRest V γs Dm P (.queued si) ⊢ ∃ (B : RegB) (q : Qp),
      wsReqF P.ws go!"rev" ↦{DFrac.own q} B.rr ∗ startOk V B.srr B.rr ∗
      (∀ (γs' : StreamNames) (Dm' : List v3rpc.WatchRespM) (si' : Option Nat),
        wsReqF P.ws go!"rev" ↦{DFrac.own q} B.rr -∗ upAtOpt γs' si' (createOfB P B) -∗
        wsRest V γs' Dm' P (.queued si')) := by
  simp only [wsRest]
  iintro (⟨%B, %sent, %C, %C2, %HB, #Hso, Hprod, Ha, Ha2, %HC, Hrv, Hps, -⟩ |
    ⟨#Hx, %B, %sent, %C, %C2, %q, %HB, #Hso, Hprod, Ha, Ha2, Hrv, -⟩)
  · iexists B, (1 : Qp).half
    iframe Hrv Hso
    iintro %γs' %Dm' %si' Hrv #Hup
    ileft
    iexists B, sent, C, C2
    iframe
    iframe #
    ipureintro; exact ⟨HB, HC⟩
  · iexists B, q
    iframe Hrv Hso
    iintro %γs' %Dm' %si' Hrv #Hup
    iright
    iframe Hx
    iexists B, sent, C, C2, q
    iframe
    iframe #
    ipureintro; exact HB

/-- **After a dispatch to a stopped substream's registration** (D25): its registered state with
nothing but the stop (`γx`) for the contract's facts. -/
theorem reg_post_dead (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B)
    (Dm : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange)
    (fcs : GoSlice) (lo : Nat) (sent : List Loc) (C C2 : List w64) (b : Bool) (wr : Loc)
    (d : DnInfo GF) (γend : GName) (n : Nat) :
    dghostVar P.γx DFrac.discard true ∗ regFacts V γs Dm P B X w rg fcs lo ∗ startOk V B.srr B.rr ∗
      monoListAuthOwn P.γhi 1 C ∗ monoListAuthOwn P.γh2 1 C2 ∗
      ((⌜b = true⌝ ∗ sendDone P sent wr d γend n) ∨ (⌜b = false⌝ ∗ sendFail V P sent wr d γend n)) ⊢
    wsRest V γs (Dm ++ [m]) P (.reg X) ∗ dnCap P d γend n := by
  iintro ⟨#Hx, #Hrf, #HsoB, Hauth, Hauth2, Hs⟩
  ihave #Hrf' := regFacts_mono V γs P B X w rg fcs lo (List.prefix_append Dm [m]) $$ Hrf
  simp only [wsRest]
  ihave ⟨%sent', Hprod, Hdc⟩ : iprop(∃ sent' : List Loc, sspscProducer P.γr sent' ∗ dnCap P d γend n)
    $$ [Hs]
  · icases Hs with (⟨-, Hd⟩ | ⟨-, Hf⟩)
    · iunfold sendDone at Hd
      icases Hd with ⟨Hd, Hdc⟩
      iexists _; iframe
    · iunfold sendFail at Hf
      icases Hf with ⟨Hf, -, -, Hdc⟩
      iexists _; iframe
  iframe Hdc
  iexists B, w, rg, fcs, lo, sent', C
  isplitr
  · ipureintro; exact hB
  iframe HsoB Hrf' Hprod Hauth
  isplitr
  · ileft; iexact Hx
  unfold cur2St
  iexists C2
  iframe Hauth2
  iright; ileft; iexact Hx

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
  · rcases Perennial.getElem?_snoc_cases hi with ⟨-, h⟩ | ⟨-, e⟩
    · exact h
    · exact absurd e.symm hx

/-- A list grown by a create request or not (`addCase`'s, `resume_ok`'s). -/
theorem create_or {L L' : List v3rpc.WatchReqM} (h : L' = L ∨ ∃ c, L' = L ++ [.create c]) (X : w64) :
    ∀ i : Nat, L'[i]? = some (v3rpc.WatchReqM.cancel X) → L[i]? = some (v3rpc.WatchReqM.cancel X) := by
  intro i hi
  rcases h with rfl | ⟨c, rfl⟩
  · exact hi
  · exact cancels_of_snoc (.create c) X (by intro e; cases e) (Or.inr rfl) i hi

/-- **What `run` holds of a lifetime beyond its `donec`** (D25): its token for taking the deposit;
or the deposit already taken at a reconnection's join, the substream stopped for good (`wsStopped`,
what its goroutine left). -/
def lifeTk (V : WEnv GF) (P : WsPrm GF) (L : LifePrm) : IProp GF :=
  iprop(ownTok L.γk ∨ wsStopped P ∗ stopBody V P)

/-- **A lifetime run can dispatch to** (persistent; D25): of the current generation `n` (its
`resumec` close contradicts `run`'s authority), or the substream stopped for good. -/
def genOk (P : WsPrm GF) (L : LifePrm) (n : Nat) : IProp GF :=
  iprop(⌜L.gen = n⌝ ∨ dghostVar P.γx DFrac.discard true)

instance genOk_persistent (P : WsPrm GF) (L : LifePrm) (n : Nat) :
    Persistent (genOk (GF := GF) P L n) := by
  unfold genOk; infer_instance

/-- **The current lifetime of a substream's goroutine, as `run` holds it** (D25): `run`'s half of
its `donec` field (the channel publishing `lifeQ`), its invariant, the token or the deposit
(`lifeTk`), and (unless an orphan, `orph`, whose lifetime may be of an earlier generation) that run
can dispatch to it (`genOk`). -/
def wsLife (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (P : WsPrm GF) (orph : Bool) : IProp GF :=
  iprop(∃ L : LifePrm, donecAt P.ws (lifeDn V G P L) ∗ lifeInvIs V G P L ∗ lifeTk V P L ∗
    (⌜orph = true⌝ ∨ genOk P L n))

/-- **A fresh lifetime of the current generation.** -/
theorem wsLife_fresh (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (P : WsPrm GF) (L : LifePrm)
    (o : Bool) (hg : L.gen = n) :
    donecAt P.ws (lifeDn V G P L) ∗ lifeInvIs V G P L ∗ ownTok L.γk ⊢ wsLife V G n P o := by
  iintro ⟨Hdc, #Hli, Htk⟩
  unfold wsLife lifeTk genOk
  iexists L
  iframe Hdc Hli
  isplitl [Htk]
  · ileft; iexact Htk
  iright; ileft; ipureintro; exact hg

/-- An orphan's lifetime (no dispatch to it). -/
theorem wsLife_orphan (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (P : WsPrm GF) (o : Bool) :
    wsLife V G n P o ⊢ wsLife V G n P true := by
  unfold wsLife
  iintro ⟨%L, Hdc, #Hli, Htk, -⟩
  iexists L
  iframe Hdc Hli Htk
  ileft; ipureintro; rfl

/-- **The current lifetime's `donec`, for a dispatch** (`dnCap`), and the lifetime back from it. -/
theorem wsLife_cap (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (P : WsPrm GF) :
    wsLife V G n P false ⊢
      ∃ d : DnInfo GF, dnCap P d G.γend n ∗ (donecAt P.ws d -∗ wsLife V G n P false) := by
  iintro Hl
  unfold wsLife
  icases Hl with ⟨%L, Hdc, #Hli, Htk, (%Ho | #Hg)⟩
  · cases Ho
  iexists lifeDn V G P L
  ihave #Href : iprop(□ ((lifeDn V G P L).Q -∗ monoNatAuthOwn G.γend 1 n -∗
      dghostVar P.γx DFrac.discard true)) $$ []
  · unfold genOk
    icases Hg with (%Hg | #Hx)
    · iapply lifeQ_cur V G P L n Hg
    · imodintro; iintro - -; iexact Hx
  unfold dnCap
  iframe Hdc Href
  iintro Hdc
  iexists L
  iframe Hdc Hli Htk
  iright; iexact Hg

/-- **A substream `run` made and has not seen stop**: its values, its phase (agreeing with the
maps, `phOk`), its id field, what `run` holds of it, (unit W-K) its id never cancelled unless
it stopped (`noCancelOk`), and (D25) its goroutine's current lifetime (`wsLife`). -/
def wsElem (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) (S : RunSt) (ws : Loc) :
    IProp GF :=
  iprop(∃ (P : WsPrm GF) (ph : WPh), ⌜P.ws = ws ∧ phOk S ws ph⌝ ∗ wsIs V P ∗
    wsF ws go!"id" ↦ ph.id ∗ wsRest V γs S.Dm P ph ∗ noCancelOk S P ph ∗
    wsLife V G n P ph.isOrphan)

/-- **`run`'s state at a `return`** (the deferred teardown's precondition; the local `closeErr` at
`cep`, the `closing` map at `clm`): the close error, the maps, the substreams, the wait group's
adder, `run`'s thread token, `donec` not yet closed. -/
def runExit (V : WEnv GF) (G : WgsPrm GF) (cep clm : Loc) : IProp GF :=
  iprop(∃ (γs : StreamNames) (S : RunSt) (U : GMap Loc Unit) (ce e : GoInterface) (mref : Loc)
      (s : GoSlice) (n : Nat),
    cep ↦ ce ∗ statusErrOk ce ∗ ownMap clm (DFrac.own 1) S.CL ∗
    wgsF G.wgs go!"substreams" ↦ mref ∗ ownMap mref (DFrac.own 1) S.M ∗
    wgsF G.wgs go!"resuming" ↦ s ∗ sliceOwn s S.l ∗
    wgsF G.wgs go!"closeErr" ↦ e ∗ statusErrOk e ∗ ⌜gOk S U⌝ ∗
    ghostMapAuth G.γws 1 U ∗ ([∗map] ws ↦ _u ∈ U, wsElem V G n γs S ws) ∗
    wgAdder G.wgs ∗ threadTok ∗ ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Pending ∗
    monoNatAuthOwn G.γend 1 n)

/-- **`run`'s state at the head of its loop** (but its local variables): the maps, the gRPC
stream's sender token and `respc`'s consumer side, what it knows (`S`, `gOk`), the server's tokens
it holds, the substreams it made (`U`), the wait group's adder, its thread token, `donec`. -/
def runCore (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (b n i : Nat) (clm csm : Loc) :
    IProp GF :=
  iprop(∃ (S : RunSt) (U : GMap Loc Unit) (rcv : List Loc) (mref : Loc) (s : GoSlice)
      (e : GoInterface),
    ownMap clm (DFrac.own 1) S.CL ∗ ownMap csm (DFrac.own 1) S.CS ∗
    wgsF G.wgs go!"substreams" ↦ mref ∗ ownMap mref (DFrac.own 1) S.M ∗
    wgsF G.wgs go!"resuming" ↦ s ∗ sliceOwn s S.l ∗
    wgsF G.wgs go!"closeErr" ↦ e ∗ statusErrOk e ∗
    cliSendTok (Req := v3rpc.pbWatchRequest) γs S.L ∗ sspscConsumer G.γr rcv ∗
    ⌜rcv.length = b + S.Dm.length⌝ ∗ epochSt G γs b i ∗ v3rpc.downLbW γs S.Dm ∗ ⌜gOk S U⌝ ∗
    ([∗list] i ∈ S.ansd, ansH γs i) ∗ ([∗list] X ∈ S.regs, idH γs X) ∗
    (□ [∗list] m ∈ S.Dm, respInfo m) ∗
    ghostMapAuth G.γws 1 U ∗ ([∗map] ws ↦ _u ∈ U, wsElem V G n γs S ws) ∗
    wgAdder G.wgs ∗ threadTok ∗ ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Pending ∗
    monoNatAuthOwn G.γend 1 n)

theorem runExit_of_core (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (b n i : Nat)
    (clm csm cep : Loc) (ce : GoInterface) :
    runCore V G γs b n i clm csm ∗ cep ↦ ce ∗ statusErrOk ce ⊢ runExit V G cep clm := by
  iintro ⟨Hc, Hcep, #Hce⟩
  unfold runCore
  icases Hc with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, -, Hsub, Hm, Hres, Hs, HcF, #He, -, -, -,
    -, -, %HgOk, -, -, -, Hwsa, Hels, Had, Htt, Hdn, Hgen⟩
  unfold runExit
  iexists γs, S, U, ce, e, mref, s, n
  iframe
  iframe #
  ipureintro; exact HgOk

theorem wsElem_mono (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S S' : RunSt} (ws : Loc)
    (hD : S'.Dm = S.Dm) (h : ∀ ph, phOk S ws ph → phOk S' ws ph)
    (hL : ∀ X, phOk S ws (.reg X) → ∀ i : Nat, S'.L[i]? = some (v3rpc.WatchReqM.cancel X) →
      S.L[i]? = some (v3rpc.WatchReqM.cancel X)) :
    wsElem V G n γs S ws ⊢ wsElem V G n γs S' ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  iexists P, ph
  rw [hD]
  iframe HP Hid Hrest
  isplitr
  · ipureintro; exact ⟨HPws, h ph Hph⟩
  iframe Hlife
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

/-- A fresh substream (its id field owned) is none of those `run` made. -/
theorem wsElems_fresh (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) (S : RunSt) (U : GMap Loc Unit) (ws : Loc)
    (v : w64) :
    ([∗map] w ↦ _u ∈ U, wsElem V G n γs S w) ∗ wsF ws go!"id" ↦ v ⊢
      ⌜U !! ws = none⌝ ∗ ([∗map] w ↦ _u ∈ U, wsElem V G n γs S w) ∗ wsF ws go!"id" ↦ v := by
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
    iintro ⟨%B, %w, %rg, %fcs, %lo, %sent, %C, %HB, #HsoB, #Hrf, Hprod, Hauth, Hst, Hc2⟩
    ihave #Hrf' := regFacts_mono V γs P B X w rg fcs lo (List.prefix_append Dm [m]) $$ Hrf
    iexists B, w, rg, fcs, lo, sent, C
    isplitr
    · ipureintro; exact HB
    iframe HsoB
    iframe Hrf' Hprod Hauth
    isplitl [Hst]
    · unfold cursorOk
      rw [evsSoFar_snoc_ctrl Dm m w h]
      iexact Hst
    iapply cur2St_mono V γs P B X w rg lo sent (evsSoFar_snoc_ctrl Dm m w h)
      (List.prefix_append Dm [m]) $$ Hc2
  | queued si => simp only [wsRest]; iintro H; iexact H
  | closedRun X => simp only [wsRest]; iintro H; iexact H
  | orphan => simp only [wsRest]; iintro H; iexact H
  | closed => simp only [wsRest]; iintro H; iexact H

theorem wsElem_mono' (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S S' : RunSt} (ws : Loc)
    (hD : ∀ P ph, phOk S ws ph → wsRest V γs S.Dm P ph ⊢ wsRest V γs S'.Dm P ph)
    (h : ∀ ph, phOk S ws ph → phOk S' ws ph) (hLe : S'.L = S.L) :
    wsElem V G n γs S ws ⊢ wsElem V G n γs S' ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  iexists P, ph
  ihave Hrest := hD P ph Hph $$ Hrest
  iframe HP Hid Hrest
  isplitr
  · ipureintro; exact ⟨HPws, h ph Hph⟩
  iframe Hlife
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
  icases H with ⟨%B, %w, %rg, %fcs, %lo, %sent, %C, %HB, #HsoB, #Hrf, Hprod, Hauth, Hrest, Hc2⟩
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
  ihave #Hrf' := regFacts_mono V γs P B X w rg fcs lo (List.prefix_append Dm [m]) $$ Hrf
  iexists B, w, rg, fcs, lo, sent, C
  isplitr
  · ipureintro; exact HB
  iframe HsoB
  iframe Hrf' Hprod Hauth
  isplitl [Hrest]
  · unfold cursorOk
    rw [hev]
    iexact Hrest
  iapply cur2St_mono V γs P B X w rg lo sent hev (List.prefix_append Dm [m]) $$ Hc2

/-- **A substream another response's id does not name** keeps its element across the response. -/
theorem wsElem_recv_other (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S S' : RunSt} (ws : Loc)
    (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (hsrc : m.src = some ρ) (hD : S'.Dm = S.Dm ++ [m])
    (hX : ∀ X, phOk S ws (.reg X) → ρ.id ≠ X) (h : ∀ ph, phOk S ws ph → phOk S' ws ph)
    (hLe : S'.L = S.L) :
    mvcc.respOk ρ ∗ wsElem V G n γs S ws ⊢ wsElem V G n γs S' ws := by
  iintro ⟨#Hr, Hw⟩
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
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
    | closed => simp only [wsRest]; itrivial
  iframe Hlife
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
      rangeWatchRespOk (EM := V.WM) V.pfx P.o P.rev hiB hiA ⟨es, W64 0, false, false, m.hdr.revision⟩ ∗
      recvCmpl V P k (wrOf m h sl) ⟨es, W64 0, false, false, m.hdr.revision⟩ ∗
      notStart P k ∗ resumeF V P ⟨es, W64 0, false, false, m.hdr.revision⟩ ⊢
    recvElem V P k wr := by
  iintro ⟨#Hwr, #Hes, Hwo, #Hi0, #Hi1, #Hrok, #Hcm, #Hns, #Hrf⟩
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
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe Hns Hrf

/-- **What a promised completeness says of a watch** (pure; K2e-7d): its start revision was read,
non-zero, and its registered range covers exactly the keys under its key. -/
theorem cpl_facts (V : WEnv GF) (P : WsPrm GF) (B : RegB) (X : w64) (rg : mvcc.WatchRange)
    (hok : wsReqOk V.pfx P) (hc : P.γ.cpl = cplOf P) (hcpl : P.γ.cpl = true) (hB : regBOk P B)
    (hcr : v3rpc.createRangeOk (createOfB P B) X rg) :
    B.srr = true ∧ 1 ≤ sint.Z B.rr ∧ (∀ k, rg.covers k = true ↔ P.o.key <+: k) ∧
      rg.startRev = B.rr ∧ rg.id = X := by
  obtain ⟨hsr, hr1⟩ := hB.2.2 hcpl
  rw [hc] at hcpl
  unfold cplOf cplCond at hcpl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcpl
  obtain ⟨-, hk, he, hff, -⟩ := hcpl
  obtain ⟨-, -, -, -, hkey, hed, -, -⟩ := hok
  refine ⟨hsr, hr1, ?_, hcr.2.1, hcr.2.2.1⟩
  · have := covers_prefix (createOfB P B) X rg hcr (by show P.key ≠ []; rw [hkey]; exact hk)
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
theorem prog_cmpl (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B) (Dm : List v3rpc.WatchRespM)
    (j : Nat) (m : v3rpc.WatchRespM) (x : mvcc.RespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange)
    (fcs : GoSlice) (lo : Nat) (c2 : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (r : RespModel) (hj : Dm.length = j) (hsrc : m.src = some x) (hxe : x.evs = [])
    (hlive : v3rpc.idLive Dm X) (hX1 : X ≠ W64 (-1)) (hxid : x.id = X ∨ x.id = W64 (-1))
    (hok : wsReqOk V.pfx P) (hcplP : P.γ.cpl = cplOf P) (hcpl : P.γ.cpl = true)
    (hst : V.R.γ.st = V.R.E.γ) (hv : ¬ watchErr v)
    (hr : r.events = [] ∧ r.created = false ∧ r.canceled = false ∧ r.compactRev = W64 0 ∧
      r.hdrRev = m.hdr.revision) (hwc : w ∈ x.cov) :
    cur2Ok V γs B.rr Dm X w rg lo c2 ∗ v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs Dm ∗
      regFacts V γs Dm P B X w rg fcs lo ∗ startOk V B.srr B.rr ∗ srvLogsSmall V.R ∗
      watchLaws V ⊢
      |={⊤}=> ∃ c2' : w64, watchRespOk (EM := V.WM) P.o.key c2 c2' v r ∗
        cur2Ok V γs B.rr (Dm ++ [m]) X w rg lo c2' := by
  iintro ⟨#Hc, #Hmv, #Hdn, #Hrf, #Hso, #Hsm, #Hlaws⟩
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
  icases Hrf with ⟨%Hcr, #Hwi, #Hfcs, -, -, -⟩
  obtain ⟨hsr, hrev1, hcov, hstart, hid⟩ := cpl_facts V P B X rg hok hcplP hcpl hB Hcr
  ihave %Hlo := cpl_lo V w rg fcs lo B.rr hstart hrev1 $$ Hwi
  ihave #Hwi' := Hwi
  iunfold mvcc.watcherIs at Hwi'
  icases Hwi' with ⟨%γw0, %C0, -, #Hwfix, -, -, -⟩
  ihave %Hfe := Hfwd $$ %w %rg %fcs Hwfix
  have hfe := Hfe (by rw [hid]; exact hX1) (by rw [hid]; exact hlive) (by rw [hid]; exact hxid)
  ihave ⟨%Lc, %dd, %p, #HLc, %Hcc⟩ := cmpl_cov V L x γc pre w rg fcs lo hfe (by omega) $$ [Hcfw Hwi Hfcs]
  · iframe Hcfw Hwi Hfcs
  obtain ⟨hpx, hp63, hE, hd1, hd2, hd3, hlop⟩ := Hcc
  have hdd : dd = p + 1 := by omega
  subst hdd
  ihave %Hq := cmpl_mono V γs B.rr L X w rg lo c2 x γc pre γo γa Lc p Hγ.2.2.1 Hγ.2.2.2 Hfr.2
    (hxid.symm.imp (fun h => h) (fun h => h)) hxe hE hlop Hlo hrev1 hpx hp63 $$ [Hc Hax Hsl0 Hrr]
  · iframe Hc Hax Hsl0 Hrr
  obtain ⟨q, hqc, hqp⟩ := Hq
  iunfold startOk at Hso
  icases Hso with (%hf | #Hr0)
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
  -- (W3) the covered log, as the contract's model sees it
  ihave #HsLc := mvcc.evLog_sealed _ _ $$ HLc
  ihave #Hsm' := Hsm
  iunfold srvLogsSmall at Hsm'
  ihave %HLs := Hsm' $$ %Lc HsLc
  ihave #Hlaws' := Hlaws
  iunfold watchLaws at Hlaws'
  icases Hlaws' with ⟨-, -, -, #Hconv⟩
  ihave HHWL0 := Hconv $$ %Lc HLc %HLs
  imod HHWL0 with #HWL
  imodintro
  iapply cmpl_prog V γs B.rr L m x X w rg lo c2 P.o.key hcov hst Lc (p + 1) p q hpx hp63 hqc hqp hE
    (Nat.le_refl _) (Or.inl (Nat.le_refl _)) hd3 hlop Hlo hrev1 hsnoc hsrc hxe hlive v r hv
    ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.trans Hm.2.1⟩
  iframe Hc HLc Hsm HWL Hlaws Hr0 Hpos

/-- **The second cursor, pending the dispatch's outcome** (K2e-7d): `γh2`'s positions, two more
than the responses dispatched before (the new one's), the last the cursor after the response. -/
def cur2Pend (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF)
    (B : RegB) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc)
    (C2 : List w64) :
    IProp GF :=
  iprop(monoListAuthOwn P.γh2 1 C2 ∗
    (⌜P.γ.cpl = false⌝ ∨ dghostVar P.γx DFrac.discard true ∨
      ⌜C2.length = sent.length + 2⌝ ∗ ∃ c2 : w64, ⌜C2.getLast? = some c2⌝ ∗
        cur2Ok V γs B.rr Dm X w rg lo c2))

/-- **A dispatch's step of the second cursor** (K2e-7d): from a step of the cursor over the
response (`hstep`, with the persistent facts `Q`, when the watch promises completeness), the
cursor's pending state and the response's completeness part (`recvCmpl`), or the substream had
stopped. -/
theorem cmpl_step (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (P : WsPrm GF) (B : RegB) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat)
    (sent : List Loc) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel)
    (Q : IProp GF) [Persistent Q]
    (hstep : P.γ.cpl = true → ∀ c2 : w64, cur2Ok V γs B.rr Dm X w rg lo c2 ∗ Q ⊢
      |={⊤}=> ∃ c2' : w64, watchRespOk (EM := V.WM) P.o.key c2 c2' v r ∗
        cur2Ok V γs B.rr (Dm ++ [m]) X w rg lo c2') :
    cur2St V γs Dm P B X w rg lo sent ∗ Q ⊢
    |={⊤}=> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P B X w rg lo sent C2 ∗
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
  imod (hstep hcpl c2) $$ [Hcur HQ] with ⟨%c2', #Hok, #Hcur'⟩
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
theorem own_cov (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (Dm : List v3rpc.WatchRespM)
    (j : Nat) (m : v3rpc.WatchRespM)
    (x : mvcc.RespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
    (hsrc : m.src = some x) (hxe : x.evs = []) (hid : x.id = X) (hX1 : X ≠ W64 (-1)) :
    v3rpc.mvccOk γs V.R.γ j m ∗ regFacts V γs Dm P B X w rg fcs lo ⊢ ⌜w ∈ x.cov⌝ := by
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
theorem reg_pre (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B) (Dm : List v3rpc.WatchRespM)
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
    srvEventIdsAssigned V.R ∗ srvLogsSmall V.R ∗ srvNoDupKeys V.R ∗ watchLaws V ∗
      startOk V B.srr B.rr ∗ v3rpc.downLbW γs Dm ∗ cur2St V γs Dm P B ρ.id w rg lo sent ∗
      v3rpc.mvccOk γs V.R.γ j m ∗ mvcc.watchRecvOk V.R.γ ρ.w rs ∗
      regFacts V γs Dm P B ρ.id w rg fcs lo ∗ sl ↦*□ ps ∗
      ([∗list] x ∈ ps.zip ρ.evs, mvcc.evIs (GF := GF) x.1 x.2) ∗
      eventsAt sl (List.zipWith evModelOf ρ.evs kvs) ∗
      monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ (∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P B Dm w rg lo hi) ∗ psAt P sent.length) ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ m.hdr.revision ⊢
    |={⊤}=> ∃ (es : List EvModel) (C' C2 : List w64), eventsAt sl es ∗ ⌜es.length = m.evs.length⌝ ∗
      (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision) ∗ monoListAuthOwn P.γhi 1 C' ∗
      (∀ wr : Loc, wr ↦□ wrOf m h sl -∗ recvElem V P sent.length wr) ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ (∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P B (Dm ++ [m]) w rg lo hi) ∗ psAt P (sent.length + 1)) ∗
      cur2Pend V γs (Dm ++ [m]) P B ρ.id w rg lo sent C2 := by
  iintro ⟨#HS3, #Hsm, #Hnd, #Hlaws, #Hso, #Hdn, Hc2, #Hmv, #Hrecv, #Hrf, #Hsl, #Hevs, #Hea, Hauth, Hst, Hrev⟩
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
  icases Hst with (#Hx | ⟨⟨%Hlen, %Hsne⟩, ⟨%hi, %Hlast, #Hcur⟩, Hps⟩)
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
  ihave Hdc := dispatch_content V P B.rr B.srr B.hb Dm m
      ρ rs ρ.id w rg fcs lo hi sl ps m.hdr.revision hsrc hρw hfilt' hps hok hpfx hst Hcr hB.1
      hB.2.1 Hhi $$ []
  · iframe #
  imod Hdc with ⟨%es, #Hes, %Hesl, #Hrok, %Hhi', #Hcut', %kvs', %Hkvs, #Hkv⟩
  -- (D25) the position marked, the resume fact's server side
  imod psAt_mark P sent.length $$ Hps with ⟨Hps, #Hns⟩
  ihave #Hrf0 : iprop((⌜ρ.evs ≠ []⌝ ∗ resumeF V P ⟨es, W64 0, false, false, m.hdr.revision⟩) ∨
      (⌜ρ.evs = []⌝ ∗ ∃ L : mvcc.Log, mvcc.notifiedLb V.R.γ L ∗
        ⌜sint.Z m.hdr.revision + 1 = (L.length : Int)⌝)) $$ []
  · by_cases hne : ρ.evs = []
    · iright
      isplitr
      · ipureintro; exact hne
      iapply mvccOk_revLb γs V.R.γ j m ρ hsrc hne $$ Hmv
    · ileft
      isplitr
      · ipureintro; exact hne
      have hw := hρw hne
      ihave #Hrecv' : mvcc.watchRecvOk V.R.γ w rs $$ []
      · rw [← hw]; iexact Hrecv
      ihave ⟨%L2, %d, #HL2, #Hrl2, %HL2d⟩ := recv_unfiltered V.R.γ w rs rg fcs lo $$ [Hrecv' Hwi Hfcs]
      · iframe #
      have h2 : evsOf Dm w ++ ρ.evs = mvcc.watchEvents L2 rg lo d := by
        rw [← evs_after Dm w rs ρ (hfilt' hne)]; exact HL2d.1
      iapply resumeF_delivered V P ⟨es, W64 0, false, false, m.hdr.revision⟩ ρ.evs kvs' (evsOf Dm w)
        L2 rg lo d hi _ Hkvs.1 Hkvs.2 hne h2
      iframe #
  have hv : ¬ watchErr (wrOf m h sl) := by
    unfold watchErr wrOf; simp [hfl.1, hfl.2.1]
  ihave Hcmp : iprop(|={⊤}=> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P B ρ.id w rg lo sent C2 ∗
      (dghostVar P.γx DFrac.discard true ∨ recvCmpl V P (sent.length : Int) (wrOf m h sl)
        ⟨es, W64 0, false, false, m.hdr.revision⟩)) $$ [Hc2]
  · by_cases hne : ρ.evs = []
    · -- an event-less response of the substream's own id: a progress notification
      have hes0 : es = [] := by
        rw [← List.length_eq_zero_iff, Hesl, hne]; rfl
      ihave %Hwc := own_cov V γs P B Dm j m ρ ρ.id w rg fcs lo hsrc hne rfl hX1 $$ [Hmv Hrf0]
      · iframe #
      iapply cmpl_step V γs Dm m P B ρ.id w rg lo sent (wrOf m h sl) _
        iprop(v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs Dm ∗
          regFacts V γs Dm P B ρ.id w rg fcs lo ∗ startOk V B.srr B.rr ∗ srvLogsSmall V.R ∗
          watchLaws V)
        (fun hc c2 => by
          iintro ⟨#Hc, #Hq1, #Hq2, #Hq3, #Hq4, #Hq5, #Hq6⟩
          iapply prog_cmpl V γs P B hB Dm j m ρ ρ.id w rg fcs lo c2 (wrOf m h sl) _ hj hsrc hne hlive
            hX1 (Or.inl rfl) hok hcplP hc hst hv ⟨hes0, rfl, rfl, rfl, rfl⟩ Hwc
          iframe #)
      iframe Hc2
      iframe #
    · -- events: the watcher's, the watch events of a watched log
      have hw := hρw hne
      ihave #Hrecv' : mvcc.watchRecvOk V.R.γ w rs $$ []
      · rw [← hw]; iexact Hrecv
      ihave ⟨%L2, %d, #HL2, -, %HL2d⟩ := recv_unfiltered V.R.γ w rs rg fcs lo $$ [Hrecv' Hwi Hfcs]
      · iframe #
      have h2 : evsOf Dm w ++ ρ.evs = mvcc.watchEvents L2 rg lo d := by
        rw [← evs_after Dm w rs ρ (hfilt' hne)]; exact HL2d.1
      have hsnoc : evsOf (Dm ++ [m]) w = evsOf Dm w ++ ρ.evs := by
        unfold evsOf
        rw [sentEvsOf_snoc, hsrc]
        simp [hw, hne]
      iapply cmpl_step V γs Dm m P B ρ.id w rg lo sent (wrOf m h sl) _
        iprop(mvcc.evLog V.R.γ.st L2 ∗ srvLogsSmall V.R ∗
          □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜ρ.evs[k]? = some ev⌝ → ⌜kvs'[k]? = some kv⌝ →
            mvcc.kvPtrFixed kv ev.kv) ∗ watchLaws V)
        (fun hc c2 => by
          iintro ⟨#Hc, #Hq1, #Hq2, #Hq3, #Hq4⟩
          obtain ⟨-, -, hcov, -, -⟩ := cpl_facts V P B ρ.id rg hok hcplP hc hB Hcr
          -- (W3) the watched log, as the contract's model sees it
          ihave #Hs2 := mvcc.evLog_sealed _ _ $$ Hq1
          ihave #Hsm2 := Hq2
          iunfold srvLogsSmall at Hsm2
          ihave %HLs2 := Hsm2 $$ %L2 Hs2
          ihave #Hq4' := Hq4
          iunfold watchLaws at Hq4'
          icases Hq4' with ⟨-, -, -, #Hconv⟩
          ihave HHWL0 := Hconv $$ %L2 Hq1 %HLs2
          imod HHWL0 with #HWL
          imodintro
          iapply cmpl_events V γs B.rr Dm m ρ.id w rg lo c2 P.o.key hcov hst L2 d ρ.evs kvs' Hkvs.2 hne
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
    ihave #Hrf : resumeF V P ⟨es, W64 0, false, false, m.hdr.revision⟩ $$ []
    · icases Hrf0 with (⟨%hne, #Hrf⟩ | ⟨%hne, %L, #HL, %HL⟩)
      · iexact Hrf
      have hes0 : es = [] := by rw [← List.length_eq_zero_iff, Hesl, hne]; rfl
      subst hes0
      ihave #Hre := recvCmpl_reached V P (sent.length : Int) (wrOf m h sl)
        ⟨[], W64 0, false, false, m.hdr.revision⟩ ⟨rfl, rfl, rfl, rfl⟩
        ⟨rfl, by simp [wrOf, hfl.1], by simp [wrOf, hfl.2.1]⟩ $$ Hcm'
      iapply resumeF_evless V P ⟨[], W64 0, false, false, m.hdr.revision⟩ L rfl HL
      iframe #
    iapply recvElem_of V P sent.length (by intro h0; exact Hsne (List.length_eq_zero_iff.1 h0)) m h
      sl es hi ((es.getLast?.map EvModel.rev).getD hi) wr hfl hhn
    iframe Hwr Hes Hwo Hi0 Hi1 Hrok Hcm' Hns Hrf
  iright
  isplitr
  · ipureintro; simp [Hlen]
  iframe Hps
  iexists ((es.getLast?.map EvModel.rev).getD hi)
  isplitr
  · ipureintro; simp
  unfold cursorOk
  iframe Hcut'
  ipureintro; exact Hhi'

/-- **After dispatching to a registered substream**: its state over the new response, whether
the send succeeded or failed. -/
theorem reg_post (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
    (sent : List Loc) (C' C2 : List w64) (b : Bool) (wr : Loc) (d : DnInfo GF) (γend : GName)
    (n : Nat) :
    regFacts V γs Dm P B X w rg fcs lo ∗ startOk V B.srr B.rr ∗ monoListAuthOwn P.γhi 1 C' ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ (∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P B (Dm ++ [m]) w rg lo hi) ∗ psAt P (sent.length + 1)) ∗
      cur2Pend V γs (Dm ++ [m]) P B X w rg lo sent C2 ∗
      ((⌜b = true⌝ ∗ sendDone P sent wr d γend n) ∨ (⌜b = false⌝ ∗ sendFail V P sent wr d γend n)) ⊢
    wsRest V γs (Dm ++ [m]) P (.reg X) ∗ dnCap P d γend n := by
  iintro ⟨#Hrf, #HsoB, Hauth, Hst, Hpend, Hs⟩
  have HB := hB
  simp only [wsRest]
  unfold cur2Pend
  icases Hpend with ⟨Ha2, Hp2⟩
  ihave #Hrf' := regFacts_mono V γs P B X w rg fcs lo (List.prefix_append Dm [m]) $$ Hrf
  icases Hs with (⟨%-, Hd⟩ | ⟨%-, Hf⟩)
  · iunfold sendDone at Hd
    icases Hd with ⟨Hd, Hdc⟩
    iframe Hdc
    iexists B, w, rg, fcs, lo, sent ++ [wr], C'
    isplitr
    · ipureintro; exact HB
    iframe HsoB
    iframe Hrf' Hd Hauth
    isplitl [Hst]
    · icases Hst with (#Hx | ⟨%Hlen, ⟨%hi, %Hl, #Hc⟩, Hps⟩)
      · ileft; iexact Hx
      · iright
        isplitr
        · ipureintro; simp [Hlen]
        isplitr
        · iexists hi
          iframe Hc
          ipureintro; exact Hl
        simp only [List.length_append, List.length_singleton]
        iexact Hps
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
    icases Hf with ⟨Hp, -, #Hx, Hdc⟩
    iframe Hdc
    iexists B, w, rg, fcs, lo, sent, C'
    isplitr
    · ipureintro; exact HB
    iframe HsoB
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
theorem bcast_pre (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B) (Dm : List v3rpc.WatchRespM)
    (j : Nat) (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange)
    (fcs : GoSlice) (lo : Nat) (sent : List Loc) (C : List w64)
    (h : Loc) (sl : GoSlice) (hsrc : m.src = some ρ) (hev : ρ.evs = [])
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false) (hhn : h ≠ null)
    (hj : Dm.length = j) (hok : wsReqOk V.pfx P) (hcplP : P.γ.cpl = cplOf P)
    (hlive : v3rpc.idLive Dm X) (hX1 : X ≠ W64 (-1)) (hid : ρ.id = W64 (-1))
    (hst : V.R.γ.st = V.R.E.γ) :
    hdrAt h m.hdr.revision ∗ eventsAt sl [] ∗ monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ (∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P B Dm w rg lo hi) ∗ psAt P sent.length) ∗
      cur2St V γs Dm P B X w rg lo sent ∗ (⌜w ∈ ρ.cov⌝ ∨ dghostVar P.γx DFrac.discard true) ∗
      v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs Dm ∗ regFacts V γs Dm P B X w rg fcs lo ∗
      startOk V B.srr B.rr ∗ srvLogsSmall V.R ∗ watchLaws V ⊢
    |={⊤}=> ∃ C' C2 : List w64, monoListAuthOwn P.γhi 1 C' ∗
      (∀ wr : Loc, wr ↦□ wrOf m h sl -∗ recvElem V P sent.length wr) ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ (∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P B (Dm ++ [m]) w rg lo hi) ∗ psAt P (sent.length + 1)) ∗
      cur2Pend V γs (Dm ++ [m]) P B X w rg lo sent C2 := by
  iintro ⟨#Hha, #Hea, Hauth, Hst, Hc2, #Hmem, #Hmv, #Hdn, #Hrf, #Hso, #Hsm, #Hlaws⟩
  icases Hst with (#Hx | ⟨⟨%Hlen, %Hsne⟩, ⟨%hi, %Hlast, #Hcur⟩, Hps⟩)
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
  ihave Hcmp : iprop(|={⊤}=> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P B X w rg lo sent C2 ∗
      (dghostVar P.γx DFrac.discard true ∨ recvCmpl V P (sent.length : Int) (wrOf m h sl)
        ⟨[], W64 0, false, false, m.hdr.revision⟩)) $$ [Hc2]
  · icases Hmem with (%Hwc | #Hx2)
    · iapply cmpl_step V γs Dm m P B X w rg lo sent (wrOf m h sl) _
        iprop(v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs Dm ∗
          regFacts V γs Dm P B X w rg fcs lo ∗ startOk V B.srr B.rr ∗ srvLogsSmall V.R ∗
          watchLaws V)
        (fun hc c2 => by
          iintro ⟨#Hc, #Hq1, #Hq2, #Hq3, #Hq4, #Hq5, #Hq6⟩
          iapply prog_cmpl V γs P B hB Dm j m ρ X w rg fcs lo c2 (wrOf m h sl) _ hj hsrc hev hlive
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
  -- (D25) the position marked, the resume fact's server side
  imod psAt_mark P sent.length $$ Hps with ⟨Hps, #Hns⟩
  ihave ⟨%Lr, #HLr, %HLr⟩ := mvccOk_revLb γs V.R.γ j m ρ hsrc hev $$ Hmv
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
    ihave #Hre := recvCmpl_reached V P (sent.length : Int) (wrOf m h sl)
      ⟨[], W64 0, false, false, m.hdr.revision⟩ ⟨rfl, rfl, rfl, rfl⟩
      ⟨rfl, by simp [wrOf, hfl.1], by simp [wrOf, hfl.2.1]⟩ $$ Hcm'
    ihave #Hrf : resumeF V P ⟨[], W64 0, false, false, m.hdr.revision⟩ $$ []
    · iapply resumeF_evless V P ⟨[], W64 0, false, false, m.hdr.revision⟩ Lr rfl HLr
      iframe #
    iapply recvElem_of V P sent.length (by intro h0; exact Hsne (List.length_eq_zero_iff.1 h0)) m h
      sl [] hi hi wr hfl hhn
    iframe Hwr Hea Hi0 Hi1 Hcm' Hns Hrf
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
  iframe Hps
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
  iprop(□ ∀ (P : WsPrm GF) (B : RegB) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat),
    ⌜P.ws = ws⌝ -∗ regFacts V γs S.Dm P B X w rg fcs lo -∗ noCancelOk S P (.reg X) -∗
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
theorem bcast_regPair (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S : RunSt} (X : w64) (ws : Loc)
    (x : mvcc.RespM) (γc : mvcc.WatchChanNames) (pre : List mvcc.RespM) (γo : mvcc.WsStreamNames)
    (γa : GName) (hM : S.M !! X = some ws)
    (hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y)
    (hregi : γo.regi = γc.regi) (hsentl : γo.sentl = γc.sentl)
    (hfresh : ∀ m' ∈ S.Dm, m'.src ≠ some x) (hid : x.id = W64 (-1)) :
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ mvcc.chanSentLb γc (pre ++ [x]) ∗ wsElem V G n γs S ws ⊢
      wsElem V G n γs S ws ∗ □ (∃ (w : Loc) (n : Nat), mvcc.idAssigned γo X w ∗ mvcc.chanRegAt γc w n ∗
        ⌜n ≤ pre.length⌝) := by
  iintro ⟨#Hax, #Hlb, Hw⟩
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  have hph0 : ph = WPh.reg X := by
    cases ph with
    | queued si => exact absurd hM (Hph.1 X)
    | orphan => exact absurd hM (Hph.1 X)
    | closed => exact absurd hM (Hph.1 X)
    | closedRun Y => exact absurd hM (Hph.1.2.1 X)
    | reg Y => rw [hinj Y X ws Hph.1 hM]
  subst hph0
  iunfold wsRest at Hrest
  icases Hrest with ⟨%B, %w, %rg, %fcs, %lo, %sent, %C, %HB, #HsoB, #Hrg, Hprod, Hauth, Hst, Hc2⟩
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
  isplitl [Hid Hprod Hauth Hst Hc2 Hlife]
  · iexists P, .reg X
    iframe HP Hid Hnc Hlife
    isplitr
    · ipureintro; exact ⟨HPws, Hph⟩
    simp only [wsRest]
    iexists B, w, rg, fcs, lo, sent, C
    isplitr
    · ipureintro; exact HB
    iframe HsoB
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
theorem bcast_covAll (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S : RunSt} (x : mvcc.RespM)
    (γc : mvcc.WatchChanNames) (pre : List mvcc.RespM) (γo : mvcc.WsStreamNames) (γa : GName)
    (hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y)
    (hregi : γo.regi = γc.regi) (hrsn : γo.rsn = γc.rsn) (hsentl : γo.sentl = γc.sentl)
    (hfresh : ∀ m' ∈ S.Dm, m'.src ≠ some x) (hid : x.id = W64 (-1)) :
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ mvcc.chanSentLb γc (pre ++ [x]) ∗
      mvcc.regsAt γc pre.length x ∗ mvcc.respCompl γc x ∗
      savedPredOwn γo.rsn DFrac.discard (v3rpc.cancelQ γs) ∗ £ 1 ∗
      cliSendTok (Req := v3rpc.pbWatchRequest) γs S.L ∗ ([∗map] _X ↦ ws ∈ S.M, wsElem V G n γs S ws) ⊢
      |={⊤}=> cliSendTok (Req := v3rpc.pbWatchRequest) γs S.L ∗
        ([∗map] _X ↦ ws ∈ S.M, wsElem V G n γs S ws) ∗
        □ (∀ (X : w64) (ws : Loc), ⌜S.M !! X = some ws⌝ -∗ bcastCov V γs S x X ws) := by
  iintro ⟨#Hax, #Hlb, #Hra, #Hcmp, #Hcq, Hlc, Ht, Hm⟩
  ihave Hm2 := BigSepM.bigSepM_impl (Ψ := fun X ws => iprop(wsElem V G n γs S ws ∗
      □ (∃ (w : Loc) (n : Nat), mvcc.idAssigned γo X w ∗ mvcc.chanRegAt γc w n ∗ ⌜n ≤ pre.length⌝)))
      $$ Hm []
  · iintro !> %X %ws %hX Hw
    iapply bcast_regPair V G n γs X ws x γc pre γo γa hX hinj hregi hsentl hfresh hid
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
  iintro !> %P %B %w %rg %fcs %lo %HPws #Hrf #Hnc
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
theorem bcast_elem (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S S' : RunSt} (X : w64) (ws : Loc)
    (j : Nat) (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (h : Loc) (sl : GoSlice)
    (hsrc : m.src = some ρ)
    (hev : ρ.evs = []) (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false)
    (hhn : h ≠ null) (hM : S.M !! X = some ws)
    (hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y)
    (hD : S'.Dm = S.Dm ++ [m]) (hph : ∀ ph, phOk S ws ph → phOk S' ws ph) (hLe : S'.L = S.L)
    (hj : S.Dm.length = j) (hid : ρ.id = W64 (-1)) (hst : V.R.γ.st = V.R.E.γ) :
    hdrAt h m.hdr.revision ∗ eventsAt sl [] ∗ bcastCov V γs S ρ X ws ∗
      v3rpc.mvccOk γs V.R.γ j m ∗ v3rpc.downLbW γs S.Dm ∗ srvLogsSmall V.R ∗ watchLaws V ∗
      wsElem V G n γs S ws ⊢
    |={⊤}=> ∃ a : WsPrm GF × List Loc × DnInfo GF, ⌜a.1.ws = ws⌝ ∗
      sendCap V a.1 a.2.1 (fun wr => iprop(wr ↦□ wrOf m h sl)) a.2.2 G.γend n ∗
      (∀ wr : Loc, (sendDone a.1 a.2.1 wr a.2.2 G.γend n ∨ sendFail V a.1 a.2.1 wr a.2.2 G.γend n) -∗
        wsElem V G n γs S' ws) := by
  iintro ⟨#Hha, #Hea, #Hbc, #Hmv, #Hdn, #Hsm, #Hlaws, Hw⟩
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  have hph0 : ph = WPh.reg X := by
    cases ph with
    | queued si => exact absurd hM (Hph.1 X)
    | orphan => exact absurd hM (Hph.1 X)
    | closed => exact absurd hM (Hph.1 X)
    | closedRun Y => exact absurd hM (Hph.1.2.1 X)
    | reg Y => rw [hinj Y X ws Hph.1 hM]
  subst hph0
  simp only [WPh.isOrphan]
  icases wsLife_cap V G n P $$ Hlife with ⟨%d, Hcap, Hback⟩
  iunfold wsRest at Hrest
  icases Hrest with ⟨%B, %w, %rg, %fcs, %lo, %sent, %C, %HB, #HsoB, #Hrg, Hprod, Hauth, Hst, Hc2⟩
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨-, -, -, -, -, -, %HPpure, #Hso⟩
  iunfold bcastCov at Hbc
  ihave #Hmem := Hbc $$ %P %B %w %rg %fcs %lo %HPws Hrg Hnc
  imod bcast_pre V γs P B HB S.Dm j m ρ X w rg fcs lo sent C h sl hsrc hev hfl hhn hj HPpure.2.1
      HPpure.2.2 Hph.2.2.2.2.2.2.2 Hph.2.2.2.2.1 hid hst
      $$ [$Hha $Hea $Hauth $Hst $Hc2 $Hmem $Hmv $Hdn $Hrg $HsoB $Hsm $Hlaws]
    with ⟨%C', %C2, Hauth, Hrecv, Hst, Hpend⟩
  imodintro
  iexists (P, sent, d)
  isplitr
  · ipureintro; exact HPws
  isplitl [Hprod Hrecv Hcap]
  · unfold sendCap
    iframe HP Hprod
    isplitl [Hrecv]
    · iintro %wr Hwr
      iapply Hrecv $$ Hwr
    iexact Hcap
  iintro %wr Hs
  ihave ⟨Hrest, Hdc⟩ : iprop(wsRest V γs (S.Dm ++ [m]) P (.reg X) ∗
      dnCap P d G.γend n) $$ [Hs Hauth Hst Hpend]
  · icases Hs with (Hd | Hf)
    · iapply reg_post V γs P B HB S.Dm m X w rg fcs lo sent C' C2 true wr d G.γend n
      iframe Hrg HsoB Hauth Hst Hpend
      ileft; iframe Hd; ipureintro; rfl
    · iapply reg_post V γs P B HB S.Dm m X w rg fcs lo sent C' C2 false wr d G.γend n
      iframe Hrg HsoB Hauth Hst Hpend
      iright; iframe Hf; ipureintro; rfl
  iunfold dnCap at Hdc
  icases Hdc with ⟨Hdc, -⟩
  iexists P, .reg X
  isplitr
  · ipureintro; exact ⟨HPws, hph _ Hph⟩
  iframe HP Hid
  rw [hD]
  iframe Hrest
  isplitr
  · iapply noCancelOk_mono P (.reg X) (fun X _ i hi => by rw [hLe] at hi; exact hi) $$ Hnc
  iapply Hback $$ Hdc

/-- A failed dispatch publishes the substream's stop (`sendFail`'s `γx`), kept. -/
theorem post_gx (V : WEnv GF) (P : WsPrm GF) (sent : List Loc) (wr : Loc) (b : Bool)
    (d : DnInfo GF) (γend : GName) (n : Nat) :
    ((⌜b = true⌝ ∗ sendDone P sent wr d γend n) ∨ (⌜b = false⌝ ∗ sendFail V P sent wr d γend n)) ⊢
      ((⌜b = true⌝ ∗ sendDone P sent wr d γend n) ∨
        (⌜b = false⌝ ∗ sendFail V P sent wr d γend n)) ∗
        (⌜b = true⌝ ∨ dghostVar P.γx DFrac.discard true) := by
  iintro (⟨%hb, Hd⟩ | ⟨%hb, Hf⟩)
  · isplitl
    · ileft; iframe Hd; ipureintro; exact hb
    ileft; ipureintro; exact hb
  · iunfold sendFail at Hf
    icases Hf with ⟨Hp, Hr, #Hx, Hdc⟩
    isplitl
    · iright; isplitr
      · ipureintro; exact hb
      iunfold sendFail; iframe Hp Hr Hx Hdc
    iright; iexact Hx

/-- **An id in `substreams`** is registered and not `-1` (its substream's phase says so). -/
theorem M_entry_facts (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S : RunSt} {U : GMap Loc Unit} {X : w64}
    {ws : Loc} (hg : gOk S U) (hM : S.M !! X = some ws) :
    ([∗map] ws' ↦ _u ∈ U, wsElem V G n γs S ws') ⊢
      ⌜X ∈ S.regs ∧ X ≠ W64 (-1)⌝ ∗ ([∗map] ws' ↦ _u ∈ U, wsElem V G n γs S ws') := by
  iintro Hels
  have hU : U !! ws = some () := hg.1 X ws hM
  icases (BigSepM.bigSepM_delete hU).1 $$ Hels with ⟨Hw, Hels⟩
  iunfold wsElem at Hw
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  have Hf : X ∈ S.regs ∧ X ≠ W64 (-1) := by
    cases ph with
    | queued si => exact absurd hM (Hph.1 X)
    | orphan => exact absurd hM (Hph.1 X)
    | closed => exact absurd hM (Hph.1 X)
    | reg Y =>
      have := hg.2.1 X Y ws hM Hph.1; subst this; exact ⟨Hph.2.2.2.1, Hph.2.2.2.2.1⟩
    | closedRun Y => exact absurd hM (Hph.1.2.1 X)
  isplitr
  · ipureintro; exact Hf
  iapply (BigSepM.bigSepM_delete hU).2
  iframe Hels
  unfold wsElem
  iexists P, ph
  iframe HP Hid Hrest Hnc Hlife
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
    (sl : GoSlice) (k : Nat) (hi rv : w64) (wr : Loc)
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = true) (hhn : h ≠ null) :
    wr ↦□ wrOf m h sl ∗ eventsAt sl [] ∗ hdrAt h m.hdr.revision ∗
      monoListIdxOwn P.γhi k hi ∗ monoListIdxOwn P.γhi (k + 1) hi ∗
      recvCmpl V P (k : Int) (wrOf m h sl) ⟨[], W64 0, false, true, m.hdr.revision⟩ ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} rv ⊢
    recvElem V P (k : Int) wr := by
  iintro ⟨#Hwr, #Hes, #Hha, #Hi0, #Hi1, #Hcm, Hrv⟩
  unfold recvElem
  ileft
  iexists wrOf m h sl, ⟨[], W64 0, false, true, m.hdr.revision⟩, hi, hi
  simp only [wrOf, Int.toNat_natCast, ↓reduceIte]
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
    (EtcdWatchNames.mk γr G.γws G.γws false) null null γr G.γws G.γws G.γws false G.γws

/-- Some `donec` (for a dispatch with no target). -/
def dummyDn (G : WgsPrm GF) : DnInfo GF := ⟨null, G.γreq, iprop(True)⟩

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

/-- **What the teardown needs of a substream's current lifetime** (D25): its values
(`closeSubstream`'s), the lifetime (its `donec`, to wait for, its invariant and `run`'s token, to
take what the goroutine leaves). -/
def lifeE (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (ws : Loc) : IProp GF :=
  iprop(∃ (P : WsPrm GF) (L : LifePrm), ⌜P.ws = ws⌝ ∗ wsIs V P ∗
    donecAt ws (lifeDn V G P L) ∗ lifeInvIs V G P L ∗ lifeTk V P L)

theorem wsElem_split (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) (S : RunSt) (ws : Loc) :
    wsElem V G n γs S ws ⊢ idE ws ∗ closerE V S ws ∗ lifeE V G n ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  subst HPws
  isplitl [Hid]
  · unfold idE; iexists _; iexact Hid
  isplitl [Hrest]
  · unfold closerE
    iexists ph
    isplitr
    · ipureintro; exact Hph
    cases ph with
    | queued si =>
      simp only [wsRest]
      unfold closerRes recvcCloser
      icases Hrest with (⟨%B, %sent, %C, %C2, -, -, Hprod, -⟩ | ⟨-, %B, %sent, %C, %C2, %q, -, -, Hprod, -⟩)
      · iexists P, sent
        iframe HP Hprod
        ipureintro; rfl
      · iexists P, sent
        iframe HP Hprod
        ipureintro; rfl
    | reg X =>
      unfold wsRest closerRes recvcCloser
      icases Hrest with ⟨%B, %w, %rg, %fcs, %lo, %sent, %C, -, -, -, Hprod, -⟩
      iexists P, sent
      iframe HP Hprod
      ipureintro; rfl
    | closedRun X => unfold closerRes; itrivial
    | orphan => unfold closerRes; itrivial
    | closed => unfold closerRes; itrivial
  iunfold wsLife at Hlife
  icases Hlife with ⟨%L, Hdc, #Hli, Htk, -⟩
  unfold lifeE
  iexists P, L
  iframe HP Hdc Hli Htk
  ipureintro; rfl

theorem wsElems_split (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) (S : RunSt) (U : GMap Loc Unit) :
    ([∗map] ws ↦ _u ∈ U, wsElem V G n γs S ws) ⊢
      ([∗map] ws ↦ _u ∈ U, idE ws) ∗ ([∗map] ws ↦ _u ∈ U, closerE V S ws) ∗
      ([∗map] ws ↦ _u ∈ U, lifeE V G n ws) := by
  refine (BigSepM.bigSepM_mono_of_forall (fun {_ _} => wsElem_split V G n γs S _)).trans ?_
  rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]

/-- **Taking what a goroutine stopped for good left** (D25): its whole membership token (posted on
`closingc`) says its lifetime is no longer running, `run`'s token that the deposit is still there,
`run`'s generation authority (or the substream's stop) that the lifetime was not resumed; unless
`run` took the deposit at a reconnection's join already. -/
theorem take_stop (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (P : WsPrm GF) (L : LifePrm) (ws : Loc)
    (hws : P.ws = ws) :
    £ 1 ∗ lifeInvIs V G P L ∗ lifeTk V P L ∗ ghostMapElem G.γws ws (DFrac.own 1) () ∗
      monoNatAuthOwn G.γend 1 n ⊢
    |={⊤}=> stopBody V P ∗ ghostMapElem G.γws ws (DFrac.own 1) () ∗ monoNatAuthOwn G.γend 1 n := by
  subst hws
  iintro ⟨Hlc, #Hli, Hlt, Hel, Ha⟩
  unfold lifeTk
  icases Hlt with (Htk | ⟨-, Hsb⟩)
  rotate_left
  · imodintro; iframe
  iinv Hli with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑lifeN) $$ Hlc Hi with Hi
  iunfold lifeSt at Hi
  icases Hi with (⟨-, Hmh⟩ | ⟨#Ht, (⟨#Hstp, (Hsb | Htk2)⟩ | ⟨#Hlb, Hrb⟩)⟩)
  · icombine Hmh Hel gives %Hv
    exfalso
    obtain ⟨Hv, _⟩ := Hv
    revert Hv
    simp only [CMRA.Valid, DFrac.op_own]
    intro h
    have : (1 / 2 : Rat) + 1 ≤ 1 := h
    grind
  · imod Hclose $$ [Htk] with -
    · inext; iunfold lifeSt; iright; iframe Ht; ileft; iframe Hstp; iright; iexact Htk
    imodintro; iframe
  · iexfalso; iapply ownTok_excl; iframe
  · icases Hrb with (Hrb | Htk2)
    · unfold resumeBody
      icases Hrb with ⟨%k0, %rv0, %rcv, %nr, %bl, %dc, -, -, -, -, -, -, -, -, Hel2⟩
      icombine Hel Hel2 gives %Hv
      exfalso
      obtain ⟨Hv, _⟩ := Hv
      revert Hv
      simp only [CMRA.Valid, DFrac.op_own]
      intro h
      have : (1 : Rat) + 1 ≤ 1 := h
      grind
    · iexfalso; iapply ownTok_excl; iframe

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

end EtcdGrove
end Perennial
