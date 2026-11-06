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
public import Proof.go_etcd_io.etcd.client.v3.WatchFire

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The answer of the request at up position `i` (the server's token, held by `run`; strict M1: of
the run the stream's auxiliary name publishes). -/
def ansH (γs : StreamNames) (i : Nat) : IProp GF :=
  iprop(∃ r : v3rpc.WRun GF, streamAuxIs γs (v3rpc.auxOf r) ∗ v3rpc.ansTok r.γa i)

/-- The token of the registered watch id `X` (the server's, held by `run`; strict M1: the run's
id token `v3rpc.idTok`, in place of mvcc's). -/
def idH (γs : StreamNames) (X : w64) : IProp GF :=
  iprop(∃ r : v3rpc.WRun GF, streamAuxIs γs (v3rpc.auxOf r) ∗ v3rpc.idTok r.γtok X)

/-- The create request of a watch. -/
abbrev createOfP (P : WsPrm GF) : v3rpc.CreateReqM := createOf P.key P.ed P.rev P.pn P.sr P.bd

/-- (D25) The create request of a registration's base. -/
abbrev createOfB (P : WsPrm GF) (B : RegB) : v3rpc.CreateReqM :=
  createOf P.key P.ed B.rr P.pn B.srr P.bd

/-- **A registered substream's place in the run** (persistent; K2e-7d; strict M1: the run's
registry entry and received list, in place of mvcc's watcher and channel): the run's registry
entry of the id `X` (its range `rg`, first revision `lo`, stamp `k`), a snapshot `l` of the run's
received list from its created response (at least `k` long), whose responses of id `-1` were all
sent down before the created one (among `L`). -/
def regSnap (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (X : w64) (rg : mvcc.WatchRange)
    (lo : Nat) : IProp GF :=
  iprop(∃ (r : v3rpc.WRun GF) (k : Nat) (l : List mvcc.api.WResp) (L : List v3rpc.WatchRespM),
    streamAuxIs γs (v3rpc.auxOf r) ∗ v3rpc.regIs r.γreg X ⟨rg, lo, k⟩ ∗ v3rpc.rcvLb r.γr l ∗
    ⌜k ≤ l.length ∧ L <+: Dm ∧ ∀ (n : Nat) (y : mvcc.api.WResp), l[n]? = some y →
      y.id = W64 (-1) → ∃ m' ∈ L, m'.src = some (n, y)⌝)

instance regSnap_persistent (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (X : w64)
    (rg : mvcc.WatchRange) (lo : Nat) : Persistent (regSnap (GF := GF) γs Dm X rg lo) := by
  unfold regSnap; infer_instance

/-- **A registered substream's watcher** (persistent): the watcher the server registered for its
create at the id `X` (range `rg`, first revision `lo`: at least the create's start revision, which
it is unless `0`; K2e-7d: its place in the run, `regSnap`); (G2) the row of its responses with
events (`wsRow`, from the created response's check). Strict M1: the run's registry entry, in
place of mvcc's `watcherIs`/`idAssigned`. -/
def regFacts (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF) (B : RegB)
    (X : w64) (rg : mvcc.WatchRange) (lo : Nat) : IProp GF :=
  iprop(⌜v3rpc.createRangeOk (createOfB P B) X rg ∧ sint.Z B.rr ≤ (lo : Int) ∧
      (B.rr ≠ W64 0 → (lo : Int) = sint.Z B.rr)⌝ ∗
    regSnap γs Dm X rg lo ∗ wsRow V P)

instance regFacts_persistent (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (P : WsPrm GF) (B : RegB) (X : w64) (rg : mvcc.WatchRange) (lo : Nat) :
    Persistent (regFacts V γs Dm P B X rg lo) := by
  unfold regFacts; infer_instance

/-- `regFacts` over more responses. -/
theorem regFacts_mono (V : WEnv GF) (γs : StreamNames) {Dm Dm' : List v3rpc.WatchRespM}
    (P : WsPrm GF) (B : RegB) (X : w64) (rg : mvcc.WatchRange) (lo : Nat)
    (hp : Dm <+: Dm') : regFacts V γs Dm P B X rg lo ⊢ regFacts V γs Dm' P B X rg lo := by
  unfold regFacts regSnap
  iintro ⟨%H1, ⟨%r, %k, %l, %L, #Ha, #Hi, #Hl, %Hp⟩, #H7⟩
  iframe H7
  isplitr
  · ipureintro; exact H1
  iexists r, k, l, L
  iframe Ha Hi Hl
  ipureintro; exact ⟨Hp.1, Hp.2.1.trans hp, Hp.2.2⟩

/-- The events of the watch id `X` received so far (`Dm`), in order. -/
abbrev evsSoFar (Dm : List v3rpc.WatchRespM) (X : w64) : List mvcc.EvM := evsOf Dm X

/-- **The dispatch cursor** `hi` of a registered substream (persistent): the last event's revision
dispatched so far (`rev - 1` if none), the events so far a cut of the watcher's events of a
certified log (strict M1: the member's `histLb`, in place of mvcc's `idxSealed`). -/
def cursorOk (V : WEnv GF) (P : WsPrm GF) (B : RegB) (Dm : List v3rpc.WatchRespM) (X : w64)
    (rg : mvcc.WatchRange) (lo : Nat) (hi : w64) : IProp GF :=
  iprop(⌜(evsSoFar Dm X = [] ∧ hi = B.hb) ∨
      (∃ e, (evsSoFar Dm X).getLast? = some e ∧ hi = e.kv.modRev)⌝ ∗
    (⌜evsSoFar Dm X = []⌝ ∨ ∃ (L1 : mvcc.Log) (d1 : Nat), □ V.W.histLb L1 ∗
      ⌜evsSoFar Dm X = mvcc.watchEvents L1 rg lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length⌝))

instance cursorOk_persistent (V : WEnv GF) (P : WsPrm GF) (B : RegB) (Dm : List v3rpc.WatchRespM)
    (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (hi : w64) :
    Persistent (cursorOk V P B Dm X rg lo hi) := by
  unfold cursorOk; infer_instance

/-- **The second cursor's positions** (D48): `γh2`'s list, each a position of the stream
(`posQ`: the watch's start or a revision of a state the read update fired at), unless the watch promises no
completeness or the substream stopped. -/
def cur2Places (P : WsPrm GF) (C2 : List w64) : IProp GF :=
  iprop(monoListAuthOwn P.γh2 1 C2 ∗
    (⌜P.γ.cpl = false⌝ ∨ dghostVar P.γx DFrac.discard true ∨ [∗list] c ∈ C2, posQ P.o P.Q c))

/-- A stopped substream's positions. -/
theorem cur2Places_dead (P : WsPrm GF) (C2 : List w64) :
    monoListAuthOwn P.γh2 1 C2 ∗ dghostVar P.γx DFrac.discard true ⊢ cur2Places P C2 := by
  unfold cur2Places
  iintro ⟨Ha, #Hx⟩
  iframe Ha
  iright; ileft; iexact Hx

/-- The watch's start, its first position. -/
theorem cur2Places_start (P : WsPrm GF) (hro : P.o.base.rev = P.rev)
    (h1 : P.γ.cpl = true → 1 ≤ sint.Z P.rev) :
    monoListAuthOwn P.γh2 1 [P.rev - W64 1] ⊢ cur2Places P [P.rev - W64 1] := by
  unfold cur2Places
  iintro Ha
  iframe Ha
  cases hc : P.γ.cpl
  · ileft; ipureintro; rfl
  iright; iright
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ c => posQ P.o P.Q c)).2
  unfold posQ; ileft; ipureintro
  have := h1 hc
  rw [hro]; word

/-- The positions' list, with its last position's fact. -/
theorem cur2Places_last (P : WsPrm GF) (C2 : List w64) (c : w64)
    (h : C2.getLast? = some c) :
    cur2Places P C2 ⊢ cur2Places P C2 ∗
      (⌜P.γ.cpl = false⌝ ∨ dghostVar P.γx DFrac.discard true ∨ posQ P.o P.Q c) := by
  unfold cur2Places
  iintro ⟨Ha, (%Hf | #Hx | #Hl)⟩
  · iframe Ha; isplitl []
    · ileft; ipureintro; exact Hf
    ileft; ipureintro; exact Hf
  · iframe Ha; isplitl []
    · iright; ileft; iexact Hx
    iright; ileft; iexact Hx
  · have hm : c ∈ C2 := List.mem_of_getLast? h
    ihave #Hc := (BigSepL.bigSepL_mem (Φ := fun c => posQ P.o P.Q c) hm) $$ Hl
    iframe Ha
    isplitl []
    · iright; iright; iexact Hl
    iright; iright; iexact Hc

/-- A position appended. -/
theorem cur2Places_app (P : WsPrm GF) (C2 : List w64) (c : w64) :
    cur2Places P C2 ∗
      (⌜P.γ.cpl = false⌝ ∨ dghostVar P.γx DFrac.discard true ∨ posQ P.o P.Q c) ⊢
    |==> (cur2Places P (C2 ++ [c]) ∗ monoListLbOwn P.γh2 (C2 ++ [c])) := by
  unfold cur2Places
  iintro ⟨⟨Ha, Hs⟩, #Hc⟩
  imod monoListAuthOwn_update_app (γ := P.γh2) (l := C2) [c] $$ Ha with ⟨Ha, #Hlb⟩
  imodintro
  iframe Hlb Ha
  icases Hs with (%Hf | #Hx | #Hl)
  · ileft; ipureintro; exact Hf
  · iright; ileft; iexact Hx
  icases Hc with (%Hf | #Hx | #Hc)
  · ileft; ipureintro; exact Hf
  · iright; ileft; iexact Hx
  iright; iright
  iapply (BigSepL.bigSepL_snoc (Φ := fun _ c => posQ P.o P.Q c)).2
  iframe Hl Hc

/-- The positions' authority, and back. -/
theorem cur2Places_auth (P : WsPrm GF) (C2 : List w64) :
    cur2Places P C2 ⊢ monoListAuthOwn P.γh2 1 C2 ∗
      (monoListAuthOwn P.γh2 1 C2 -∗ cur2Places P C2) := by
  unfold cur2Places
  iintro ⟨Ha, Hs⟩
  iframe Ha
  iintro Ha
  iframe Ha Hs

/-- **The second dispatch cursor of a registered substream** (K2e-7d; `sent` the responses
dispatched): `γh2`'s positions `C2`, and, unless the watch promises no completeness or the
substream stopped, one more than the responses, the last the cursor (`cur2Ok`). -/
def cur2St (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF) (B : RegB)
    (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc) : IProp GF :=
  iprop(∃ C2 : List w64, cur2Places P C2 ∗
    (⌜P.γ.cpl = false⌝ ∨ dghostVar P.γx DFrac.discard true ∨
      ⌜C2.length = sent.length + 1⌝ ∗ ∃ c2 : w64, ⌜C2.getLast? = some c2⌝ ∗
        cur2Ok V γs B.rr Dm X rg lo c2))

/-- `cur2St` over more responses, none of the watcher's events. -/
theorem cur2St_mono (V : WEnv GF) (γs : StreamNames) {Dm Dm' : List v3rpc.WatchRespM}
    (P : WsPrm GF) (B : RegB) (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc)
    (h : evsOf Dm' X = evsOf Dm X) (hp : Dm <+: Dm') :
    cur2St V γs Dm P B X rg lo sent ⊢ cur2St V γs Dm' P B X rg lo sent := by
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
    iapply cur2Ok_mono V γs B.rr X rg lo c2 h hp $$ Hc

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
      monoListAuthOwn P.γhi 1 C ∗ cur2Places P C2 ∗
      ⌜C.length = sent.length + 1 ∧ C.getLast? = some B.hb ∧
        (P.γ.cpl = true → C2.length = sent.length + 1 ∧ C2.getLast? = some (B.rr - W64 1))⌝ ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} B.rr ∗ psSt P sent.length ∗
      upAtOpt γs si (createOfB P B)) ∨
    -- (D25) stopped for good when a reconnection resumed it: what its create and registration need
    (dghostVar P.γx DFrac.discard true ∗ ∃ (B : RegB) (sent : List Loc) (C C2 : List w64) (q : Qp),
      ⌜regBOk P B⌝ ∗ startOk V B.srr B.rr ∗ sspscProducer P.γr sent ∗
      monoListAuthOwn P.γhi 1 C ∗ monoListAuthOwn P.γh2 1 C2 ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own q} B.rr ∗ upAtOpt γs si (createOfB P B)))
  | .reg X => iprop(∃ (B : RegB) (rg : mvcc.WatchRange) (lo : Nat)
      (sent : List Loc) (C : List w64),
      ⌜regBOk P B⌝ ∗ startOk V B.srr B.rr ∗
      regFacts V γs Dm P B X rg lo ∗ sspscProducer P.γr sent ∗ monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ (∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P B Dm X rg lo hi) ∗ psAt P sent.length) ∗
      cur2St V γs Dm P B X rg lo sent)
  | .closedRun _ => dghostVar P.γx DFrac.discard true
  | .closed => dghostVar P.γx DFrac.discard true
  | .orphan => iprop(True)

/-- A request's revision is its `Op`'s. -/
theorem wsReqOk_rev {pfx : GoString} {P : WsPrm GF} (h : wsReqOk pfx P) : P.o.base.rev = P.rev := by
  have h1 := h.1
  simp only [OpFull.isRangeWatch, decide_eq_true_eq] at h1
  exact h1.2.1

/-- **A fresh substream's queued state** (its first create, base `regB0`). -/
theorem queued_fresh (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF)
    (si : Option Nat) (hB : regBOk P (regB0 P)) (hro : P.o.base.rev = P.rev) :
    startOk V P.sr P.rev ∗ sspscProducer P.γr ([] : List Loc) ∗
      monoListAuthOwn P.γhi 1 [P.rev - W64 1] ∗ monoListAuthOwn P.γh2 1 [P.rev - W64 1] ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} P.rev ∗ psQ P ∗
      upAtOpt γs si (createOfP P) ⊢
    wsRest V γs Dm P (.queued si) := by
  iintro ⟨#Hso, Hprod, Ha, Ha2, Hrv, Hps, Hup⟩
  ihave Ha2 := cur2Places_start P hro (fun h => (hB.2.2 h).2) $$ Ha2
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
    (Dm : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM) (X : w64) (rg : mvcc.WatchRange)
    (lo : Nat) (sent : List Loc) (C C2 : List w64) (b : Bool) (wr : Loc)
    (d : DnInfo GF) (γend : GName) (n : Nat) :
    dghostVar P.γx DFrac.discard true ∗ regFacts V γs Dm P B X rg lo ∗ startOk V B.srr B.rr ∗
      monoListAuthOwn P.γhi 1 C ∗ monoListAuthOwn P.γh2 1 C2 ∗
      ((⌜b = true⌝ ∗ sendDone P sent wr d γend n) ∨ (⌜b = false⌝ ∗ sendFail V P sent wr d γend n)) ⊢
    wsRest V γs (Dm ++ [m]) P (.reg X) ∗ dnCap P d γend n := by
  iintro ⟨#Hx, #Hrf, #HsoB, Hauth, Hauth2, Hs⟩
  ihave #Hrf' := regFacts_mono V γs P B X rg lo (List.prefix_append Dm [m]) $$ Hrf
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
  iexists B, rg, lo, sent', C
  isplitr
  · ipureintro; exact hB
  iframe HsoB Hrf' Hprod Hauth
  isplitr
  · ileft; iexact Hx
  unfold cur2St
  iexists C2
  isplitl [Hauth2]
  · iapply cur2Places_dead; iframe Hauth2 Hx
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
  iprop(∃ (P : WsPrm GF) (ph : WPh), ⌜P.ws = ws ∧ phOk S ws ph ∧
      streamKeyOf (metadata.outgoingOf (GoInterface.ok P.ctx)) =
        streamKeyOf (metadata.outgoingOf (GoInterface.ok G.ctx))⌝ ∗ wsIs V P ∗
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
    ⌜rcv.length = b + S.Dm.length⌝ ∗
    (∃ tok, epochSt G γs b i tok ∗
      ⌜∃ md, tok = auth.mdTokenOf md ∧ clientAttemptMd V.conn (GoInterface.ok G.ctx) md⌝) ∗
    v3rpc.downLbW γs S.Dm ∗
    ⌜gOk S U⌝ ∗
    ([∗list] i ∈ S.ansd, ansH γs i) ∗ ([∗list] X ∈ S.regs, idH γs X) ∗
    ghostMapAuth G.γws 1 U ∗ ([∗map] ws ↦ _u ∈ U, wsElem V G n γs S ws) ∗
    wgAdder G.wgs ∗ threadTok ∗ ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Pending ∗
    monoNatAuthOwn G.γend 1 n)

theorem runExit_of_core (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (b n i : Nat)
    (clm csm cep : Loc) (ce : GoInterface) :
    runCore V G γs b n i clm csm ∗ cep ↦ ce ∗ statusErrOk ce ⊢ runExit V G cep clm := by
  iintro ⟨Hc, Hcep, #Hce⟩
  unfold runCore
  icases Hc with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, -, Hsub, Hm, Hres, Hs, HcF, #He, -, -, -,
    -, -, %HgOk, -, -, Hwsa, Hels, Had, Htt, Hdn, Hgen⟩
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
  iintro ⟨%P, %ph, ⟨%HPws, %Hph, %Hkey⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  iexists P, ph
  rw [hD]
  iframe HP Hid Hrest
  isplitr
  · ipureintro; exact ⟨HPws, h ph Hph, Hkey⟩
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

theorem evsSoFar_snoc_ctrl (Dm : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM) (X : w64)
    (h : m.src = none) : evsSoFar (Dm ++ [m]) X = evsSoFar Dm X := by
  unfold evsSoFar evsOf
  rw [sentEvsOf_snoc, h]; simp

theorem wsRest_snoc_ctrl (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (P : WsPrm GF) (ph : WPh) (h : m.src = none) :
    wsRest V γs Dm P ph ⊢ wsRest V γs (Dm ++ [m]) P ph := by
  cases ph with
  | reg X =>
    simp only [wsRest]
    iintro ⟨%B, %rg, %lo, %sent, %C, %HB, #HsoB, #Hrf, Hprod, Hauth, Hst, Hc2⟩
    ihave #Hrf' := regFacts_mono V γs P B X rg lo (List.prefix_append Dm [m]) $$ Hrf
    iexists B, rg, lo, sent, C
    isplitr
    · ipureintro; exact HB
    iframe HsoB
    iframe Hrf' Hprod Hauth
    isplitl [Hst]
    · unfold cursorOk
      rw [evsSoFar_snoc_ctrl Dm m X h]
      iexact Hst
    iapply cur2St_mono V γs P B X rg lo sent (evsSoFar_snoc_ctrl Dm m X h)
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
  iintro ⟨%P, %ph, ⟨%HPws, %Hph, %Hkey⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  iexists P, ph
  ihave Hrest := hD P ph Hph $$ Hrest
  iframe HP Hid Hrest
  isplitr
  · ipureintro; exact ⟨HPws, h ph Hph, Hkey⟩
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

theorem ans_fresh (γs : StreamNames) (ansd : List Nat) (i : Nat) (r : v3rpc.WRun GF) :
    ([∗list] j ∈ ansd, ansH (GF := GF) γs j) ∗ streamAuxIs γs (v3rpc.auxOf r) ∗
      v3rpc.ansTok r.γa i ⊢
      ⌜i ∉ ansd⌝ ∗ ([∗list] j ∈ ansd, ansH γs j) ∗ v3rpc.ansTok r.γa i := by
  iintro ⟨Hl, #Hax, Ht⟩
  by_cases hi : i ∈ ansd
  · icases BigSepL.bigSepL_mem_acc hi $$ Hl with ⟨H, -⟩
    unfold ansH
    icases H with ⟨%r', #Hax', Ht'⟩
    ihave %He : iprop(⌜v3rpc.auxOf r = v3rpc.auxOf r'⌝) $$ []
    · iapply streamAuxIs_agree
      isplit
      · iexact Hax
      · iexact Hax'
    obtain ⟨-, -, -, hγ⟩ := v3rpc.auxOf_inj He
    irevert Ht'; rw [← hγ]; iintro Ht'
    iexfalso
    iapply v3rpc.ansTok_excl $$ [$Ht $Ht']
  · iframe; ipureintro; exact hi

/-- Two tokens of one id are impossible. -/
theorem idTok_excl (γtok : GName) (X : w64) :
    v3rpc.idTok (GF := GF) γtok X ∗ v3rpc.idTok γtok X ⊢ False := by
  unfold v3rpc.idTok
  iintro ⟨H1, H2⟩
  ihave %H := ghostMapElem_valid_2 X γtok (DFrac.own 1) (DFrac.own 1) () () $$ H1 H2
  exfalso
  exact absurd (DFrac.valid_op_own H.1) (by simp)

theorem id_fresh (γs : StreamNames) (regs : List w64) (X : w64) (r : v3rpc.WRun GF) :
    ([∗list] Y ∈ regs, idH (GF := GF) γs Y) ∗ streamAuxIs γs (v3rpc.auxOf r) ∗
      v3rpc.idTok r.γtok X ⊢
      ⌜X ∉ regs⌝ ∗ ([∗list] Y ∈ regs, idH γs Y) ∗ v3rpc.idTok r.γtok X := by
  iintro ⟨Hl, #Hax, Ht⟩
  by_cases hi : X ∈ regs
  · icases BigSepL.bigSepL_mem_acc hi $$ Hl with ⟨H, -⟩
    unfold idH
    icases H with ⟨%r', #Hax', Ht'⟩
    ihave %He : iprop(⌜v3rpc.auxOf r = v3rpc.auxOf r'⌝) $$ []
    · iapply streamAuxIs_agree
      isplit
      · iexact Hax
      · iexact Hax'
    obtain ⟨-, hγ, -, -⟩ := v3rpc.auxOf_inj He
    irevert Ht'; rw [← hγ]; iintro Ht'
    iexfalso
    iapply idTok_excl $$ [$Ht $Ht']
  · iframe; ipureintro; exact hi

/-- An event response of another watcher leaves a registered substream's cursor alone (strict
M1: by id, the responses' events are of their own id's). -/
theorem wsRest_snoc_other (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (ρ : Nat × mvcc.api.WResp) (P : WsPrm GF) (X : w64)
    (hsrc : m.src = some ρ) (hX : ρ.2.id ≠ X) :
    wsRest V γs Dm P (.reg X) ⊢ wsRest V γs (Dm ++ [m]) P (.reg X) := by
  iintro H
  simp only [wsRest]
  icases H with ⟨%B, %rg, %lo, %sent, %C, %HB, #HsoB, #Hrf, Hprod, Hauth, Hrest, Hc2⟩
  have hev : evsSoFar (Dm ++ [m]) X = evsSoFar Dm X := by
    unfold evsSoFar evsOf
    rw [sentEvsOf_snoc, hsrc]
    simp [hX]
  ihave #Hrf' := regFacts_mono V γs P B X rg lo (List.prefix_append Dm [m]) $$ Hrf
  iexists B, rg, lo, sent, C
  isplitr
  · ipureintro; exact HB
  iframe HsoB
  iframe Hrf' Hprod Hauth
  isplitl [Hrest]
  · unfold cursorOk
    rw [hev]
    iexact Hrest
  iapply cur2St_mono V γs P B X rg lo sent hev (List.prefix_append Dm [m]) $$ Hc2

/-- **A substream another response's id does not name** keeps its element across the response. -/
theorem wsElem_recv_other (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S S' : RunSt}
    (ws : Loc) (m : v3rpc.WatchRespM) (ρ : Nat × mvcc.api.WResp) (hsrc : m.src = some ρ)
    (hD : S'.Dm = S.Dm ++ [m])
    (hX : ∀ X, phOk S ws (.reg X) → ρ.2.id ≠ X) (h : ∀ ph, phOk S ws ph → phOk S' ws ph)
    (hLe : S'.L = S.L) :
    wsElem V G n γs S ws ⊢ wsElem V G n γs S' ws := by
  iintro Hw
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph, %Hkey⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  iexists P, ph
  rw [hD]
  iframe HP Hid
  isplitr
  · ipureintro; exact ⟨HPws, h ph Hph, Hkey⟩
  isplitl [Hrest]
  · cases ph with
    | reg X =>
      iapply wsRest_snoc_other V γs S.Dm m ρ P X hsrc (hX X Hph)
      iexact Hrest
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
      ⌜dispOk P.rev hiB hiA ⟨es, W64 0, false, false, m.hdr.revision⟩⌝ ∗
      recvCmpl V P k (wrOf m h sl) ⟨es, W64 0, false, false, m.hdr.revision⟩ ∗
      notStart P k ∗ resumeF V P ⟨es, W64 0, false, false, m.hdr.revision⟩ ∗
      □ (⌜es ≠ []⌝ → wsRow V P) ⊢
    recvElem V P k wr := by
  iintro ⟨#Hwr, #Hes, Hwo, #Hi0, #Hi1, #Hrok, #Hcm, #Hns, #Hrf, #Hrow⟩
  unfold recvElem
  ileft
  iexists wrOf m h sl, ⟨es, W64 0, false, false, m.hdr.revision⟩, hiB, hiA
  simp only [wrOf, Int.toNat_natCast, Int.natCast_eq_zero, hk, ↓reduceIte]
  iframe Hwr Hes Hwo Hi0 Hi1 Hrok
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3⟩ := hfl
    simp [hhn, h1, h2, h3, respKindOk]
  isplitr
  · iexact Hcm
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe Hns Hrf Hrow
  iapply cmpOkOf_zero

/-- **What a promised completeness says of a watch** (pure; K2e-7d): its start revision was read,
non-zero, and its registered range covers exactly the watch's range (`rangeExact`). -/
theorem cpl_facts (V : WEnv GF) (P : WsPrm GF) (B : RegB) (X : w64) (rg : mvcc.WatchRange)
    (hok : wsReqOk V.pfx P) (hc : P.γ.cpl = cplOf P) (hcpl : P.γ.cpl = true) (hB : regBOk P B)
    (hcr : v3rpc.createRangeOk (createOfB P B) X rg) :
    B.srr = true ∧ 1 ≤ sint.Z B.rr ∧
      (∀ k, rg.covers k = inRange P.o.key P.o.base.rangeEnd k) ∧
      rg.startRev = B.rr ∧ rg.id = X := by
  obtain ⟨hsr, hr1⟩ := hB.2.2 hcpl
  rw [hc] at hcpl
  obtain ⟨-, hex, -⟩ := cplCond_iff.1 hcpl
  obtain ⟨-, -, -, hkey, hed, -, -⟩ := hok
  refine ⟨hsr, hr1, ?_, hcr.2.1, hcr.2.2.1⟩
  exact hex (createOfB P B) X rg hkey hed hcr

/-- **A promised watch's registered range is the watch's range** (`cpl_facts`). -/
theorem cpl_cov (V : WEnv GF) (P : WsPrm GF) (B : RegB) (X : w64) (rg : mvcc.WatchRange)
    (hok : wsReqOk V.pfx P) (hc : P.γ.cpl = cplOf P) (hcpl : P.γ.cpl = true) (hB : regBOk P B)
    (hcr : v3rpc.createRangeOk (createOfB P B) X rg) :
    ∀ k, rg.covers k = inRange P.o.key P.o.base.rangeEnd k :=
  (cpl_facts V P B X rg hok hc hcpl hB hcr).2.2.1

/-- **A promised watch's first revision is its start revision** (`regFacts`' pure part). -/
theorem cpl_lo (rr : w64) (lo : Nat) (h : rr ≠ W64 0 → (lo : Int) = sint.Z rr)
    (hr : 1 ≤ sint.Z rr) : lo = (sint.Z rr).toNat := by
  have := h (fun e => by rw [e] at hr; simp at hr)
  omega

/-- **A registered watcher, at an event-less, non-compaction response of its own id or of `-1`**
(`progressCov` at the substream's registry entry and created response's snapshot, `regSnap`):
covered (`progCovd`), or a broadcast and the client asked to cancel it. -/
theorem regCov (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB)
    (Dm : List v3rpc.WatchRespM) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs)
    (j : Nat) (m : v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp) (X : w64)
    (rg : mvcc.WatchRange) (lo : Nat) (hsrc : m.src = some (n, x)) (hxe : x.evs = [])
    (hxc : x.compactRev = W64 0) (hX1 : X ≠ W64 (-1)) (hj : Dm.length = j)
    (hlive : v3rpc.idLive Dm X) (hxid : x.id = X ∨ x.id = W64 (-1)) :
    srvWLaws V.W ∗ v3rpc.srvOnce V.W ∗ streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗
      regFacts V γs Dm P B X rg lo ∗ v3rpc.downLbW γs Dm ⊢
      |={⊤}=> progCovd r Dm n x X rg lo ∨ (⌜x.id = W64 (-1)⌝ ∗ v3rpc.cancelQ γs X) := by
  iintro ⟨#Hl, #Ho, #Hax, #Hmv, #Hrf, #Hdn⟩
  iunfold regFacts at Hrf
  iunfold regSnap at Hrf
  icases Hrf with ⟨-, ⟨%r', %k, %l, %Lc, #Hax', #Hreg, #Hrl, %Hs⟩, -⟩
  ihave %He : iprop(⌜v3rpc.auxOf r = v3rpc.auxOf r'⌝) $$ []
  · iapply streamAuxIs_agree; isplit
    · iexact Hax
    · iexact Hax'
  obtain ⟨hreg, -, hγr, -⟩ := v3rpc.auxOf_inj He
  irevert Hreg Hrl; rw [← hreg, ← hγr]; iintro #Hreg #Hrl
  irevert Hl Ho; rw [← hrW]; iintro #Hl #Ho
  ihave #Hdn' : monoListLbOwn r.γs.down Dm $$ []
  · rw [hrs]; iunfold v3rpc.downLbW at Hdn; iexact Hdn
  imod progressCov r j m n x X ⟨rg, lo, k⟩ l Lc Dm hsrc hxe hxc hX1 Hs.1 Hs.2.1 hj Hs.2.2 hlive
    hxid $$ [Hl Ho Hmv Hreg Hrl Hdn'] with (#Hc | ⟨%Hm1, #Hq⟩)
  · iframe #
  · imodintro; ileft; iexact Hc
  imodintro; iright
  isplitr
  · ipureintro; exact Hm1
  rw [← hrs]; iexact Hq

/-- **The second cursor over an event-less mvcc response** `x` (the `j`th sent down, the `n`-th
the run received, the substream's own id `X` or `-1`, covering its watcher, `progCovd`): the
cache's contract from the cursor and the cursor after it (`cmpl_cov`, `cmpl_mono`,
`cmpl_prog`). -/
theorem prog_cmpl (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B)
    (Dm : List v3rpc.WatchRespM) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs)
    (j : Nat) (m : v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp) (X : w64)
    (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (r' : RespModel) (hj : Dm.length = j) (hsrc : m.src = some (n, x)) (hxe : x.evs = [])
    (hlive : v3rpc.idLive Dm X) (hX1 : X ≠ W64 (-1)) (hxid : x.id = X ∨ x.id = W64 (-1))
    (hok : wsReqOk V.pfx P) (hcplP : P.γ.cpl = cplOf P) (hcpl : P.γ.cpl = true)
    (hv : ¬ watchErr v)
    (hr : r'.events = [] ∧ r'.created = false ∧ r'.canceled = false ∧ r'.compactRev = W64 0 ∧
      r'.hdrRev = m.hdr.revision) (hmc : m.compactRev = W64 0) :
    cur2Ok V γs B.rr Dm X rg lo c2 ∗ streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗
      v3rpc.downLbW γs Dm ∗ regFacts V γs Dm P B X rg lo ∗ progCovd r Dm n x X rg lo ∗
      srvWLaws V.W ⊢
      |={⊤}=> ∃ c2' : w64, rawRespOk V.W P.o c2 c2' v r' ∗
        cur2Ok V γs B.rr (Dm ++ [m]) X rg lo c2' := by
  iintro ⟨#Hc, #Hax, #Hmv, #Hdn, #Hrf, #Hcov, #Hl⟩
  ihave ⟨%pre0, %Ls, %σ, %S, %Hm, #HLs, -, -, -, -⟩ := mvccOk_at r j m n x hsrc $$ Hmv
  ihave %HLD : ⌜Ls = Dm⌝ $$ []
  · iunfold v3rpc.downLbW at Hdn
    irevert HLs; rw [hrs]; iintro #HLs
    ihave %Hcmp := mono_list_lb_valid _ Ls Dm $$ HLs Hdn
    ipureintro
    exact eq_of_comparable Hcmp (by rw [hj]; exact Hm.2.2.1)
  subst HLD
  have hxc : x.compactRev = W64 0 := by
    have := congrArg v3rpc.WatchRespM.compactRev Hm.1
    simp only [v3rpc.mvccResp] at this; rw [← this]; exact hmc
  iunfold regFacts at Hrf
  icases Hrf with ⟨%Hcr, -, -⟩
  obtain ⟨hcr, -, hlo0⟩ := Hcr
  obtain ⟨hsr, hrev1, -, hstart, hid⟩ := cpl_facts V P B X rg hok hcplP hcpl hB hcr
  have hcov := cpl_cov V P B X rg hok hcplP hcpl hB hcr
  have Hlo := cpl_lo B.rr lo hlo0 hrev1
  iunfold progCovd at Hcov
  icases Hcov with ⟨%pre, %L, #Hr, #HL, %Hpc⟩
  obtain ⟨hpre, hrec, hlor, hlen, hfwe⟩ := Hpc
  have hfe := hfwe hX1 hlive hxid
  obtain ⟨dd, p, hpx, hp63, hE, hd1, hd2, hd3, hlop⟩ :=
    cmpl_cov Ls x pre X rg lo L hfe hxe hrec hlor hlen (by omega)
  have hdd : dd = p + 1 := by omega
  subst hdd
  ihave %Hq := cmpl_mono V γs B.rr Ls X rg lo c2 r j m n x L p hsrc Hm.2.2.2.2.2.2.2.2.1
    (hxid.symm.imp (fun h => h) (fun h => h)) hxe hxc hE hlop Hlo hrev1 hpx hp63 $$ [Hc Hax Hmv]
  · iframe Hc Hax Hmv
  obtain ⟨q, hqc, hqp⟩ := Hq
  ihave #Hpos : rcvAt γs pre x $$ []
  · unfold rcvAt
    iexists r
    iframe Hax Hr
  have hsnoc : evsOf (Ls ++ [m]) X = evsOf Ls X := by
    unfold evsOf
    rw [sentEvsOf_snoc, hsrc]
    simp [hxe]
  ihave #HL' : □ V.W.histLb L $$ []
  · rw [← hrW]; iexact HL
  imodintro
  iapply cmpl_prog V γs B.rr Ls m x pre X rg lo c2 P.o hcov L (p + 1) p q hpx hp63 hqc hqp hE
    (Nat.le_refl _) (Or.inl (Nat.le_refl _)) hd3 hlop Hlo hrev1 hsnoc (by rw [hpre]; exact hsrc)
    hxe hlive v r' hv
    ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.trans Hm.2.1⟩
  iframe Hc HL' Hl Hpos

/-- **The second cursor, pending the dispatch's outcome** (K2e-7d): `γh2`'s positions, two more
than the responses dispatched before (the new one's), the last the cursor after the response. -/
def cur2Pend (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF)
    (B : RegB) (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc)
    (C2 : List w64) :
    IProp GF :=
  iprop(cur2Places P C2 ∗
    (⌜P.γ.cpl = false⌝ ∨ dghostVar P.γx DFrac.discard true ∨
      ⌜C2.length = sent.length + 2⌝ ∗ ∃ c2 : w64, ⌜C2.getLast? = some c2⌝ ∗
        cur2Ok V γs B.rr Dm X rg lo c2))

/-- **A dispatch's step of the second cursor** (K2e-7d): from a step of the cursor over the
response (`hstep`, with the persistent facts `Q`, when the watch promises completeness), the
cursor's pending state and the response's completeness part (`recvCmpl`), or the substream had
stopped. -/
theorem cmpl_step (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (P : WsPrm GF) (B : RegB) (X : w64) (rg : mvcc.WatchRange) (lo : Nat)
    (sent : List Loc) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel)
    (Q : IProp GF) [Persistent Q] (hkst : P.kv.st = V.kst)
    (hstep : P.γ.cpl = true → ∀ c2 : w64, cur2Ok V γs B.rr Dm X rg lo c2 ∗ Q ⊢
      |={⊤}=> ∃ c2' : w64, rawRespOk V.W P.o c2 c2' v r ∗
        cur2Ok V γs B.rr (Dm ++ [m]) X rg lo c2') :
    cur2St V γs Dm P B X rg lo sent ∗ Q ∗ srvKVFacts V ∗ srvWLaws V.W ∗ wsAu P ⊢
    |={⊤}=> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P B X rg lo sent C2 ∗
      (dghostVar P.γx DFrac.discard true ∨ recvCmpl V P (sent.length : Int) v r) := by
  iintro ⟨Hc, #HQ, #Hkf, #Hl, #Hau⟩
  unfold cur2St
  icases Hc with ⟨%C2, Ha, (%Hf | #Hx | ⟨%Hl2, %c2, %Hlc, #Hcur⟩)⟩
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
  ihave ⟨Ha, #Hcp⟩ := cur2Places_last P C2 c2 Hlc $$ Ha
  icases Hcp with (%Hf | #Hx | #Hcp)
  · rw [hcpl] at Hf; cases Hf
  · imodintro
    iexists C2
    unfold cur2Pend
    iframe Ha
    isplitr
    · iright; ileft; iexact Hx
    ileft; iexact Hx
  imod (hstep hcpl c2) $$ [Hcur HQ] with ⟨%c2', #Hok, #Hcur'⟩
  · iframe Hcur HQ
  -- (D47) the caller's read update, fired at the response's watched log
  iunfold wsAu at Hau
  imod (raw_to_state V P.kv hkst P.o c2 c2' v r P.Q) $$ Hkf Hl Hau Hcp Hok with ⟨%σ, #HQσ, #Hsσ⟩
  ihave #Hcp' := posQ_of_resp P.o P.Q σ c2 c2' v r $$ [Hcp HQσ Hsσ]
  · iframe Hcp HQσ Hsσ
  ihave Hu := cur2Places_app P C2 c2' $$ [Ha]
  · iframe Ha; iright; iright; iexact Hcp'
  imod Hu with ⟨Ha, #Hlb⟩
  have h0 : (C2 ++ [c2'])[sent.length]? = some c2 := by
    rw [List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at Hlc
    rw [show sent.length = C2.length - 1 by omega]; exact Hlc
  have h1 : (C2 ++ [c2'])[sent.length + 1]? = some c2' := by
    rw [List.getElem?_append_right (by omega)]; simp [Hl2]
  ihave #Hi0 := monoListIdxOwn_get (γ := P.γh2) sent.length c2 h0 $$ Hlb
  ihave #Hi1 := monoListIdxOwn_get (γ := P.γh2) (sent.length + 1) c2' h1 $$ Hlb
  imodintro
  iexists C2 ++ [c2']
  unfold cur2Pend
  iframe Ha
  isplitr
  · iright; iright
    isplitr
    · ipureintro; simp [Hl2]
    iexists c2'
    iframe Hcur'
    ipureintro; simp
  iright
  unfold recvCmpl
  iright
  iexists c2, c2'
  simp only [Int.toNat_natCast]
  iframe Hi0 Hi1
  isplitr
  · iexists V.W; iexact Hok
  iexists σ
  iframe HQσ Hsσ

/-- **The events a response with events adds, from the snapshot** (`recvEvents` at the
substream's registry entry, `regSnap`): its id's received events up to it the range's of `[lo, d)`
of a certified log, its id's responses with events sent before it, then it, those received. -/
theorem reg_events (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB)
    (Dm : List v3rpc.WatchRespM) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs)
    (j : Nat) (m : v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp) (rg : mvcc.WatchRange)
    (lo : Nat) (hsrc : m.src = some (n, x)) (hX1 : x.id ≠ W64 (-1)) (hj : Dm.length = j) :
    srvWLaws V.W ∗ v3rpc.srvOnce V.W ∗ streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗
      regFacts V γs Dm P B x.id rg lo ∗ v3rpc.downLbW γs Dm ⊢
      |={⊤}=> ∃ (pre : List mvcc.api.WResp) (L : mvcc.Log) (d : Nat), □ V.W.histLb L ∗
        ⌜(x.evs ≠ [] → v3rpc.sentEvsOf Dm x.id ++ [x] =
            ((pre ++ [x]).filter (fun y => decide (y.id = x.id))).filter
              (fun y => decide (y.evs ≠ []))) ∧
          mvcc.api.recvEvs (pre ++ [x]) x.id = mvcc.watchEvents L rg lo d ∧ d ≤ L.length⌝ := by
  iintro ⟨#Hl, #Ho, #Hax, #Hmv, #Hrf, #Hdn⟩
  iunfold regFacts at Hrf
  iunfold regSnap at Hrf
  icases Hrf with ⟨-, ⟨%r', %k, %l, %Lc, #Hax', #Hreg, -, -⟩, -⟩
  ihave %He : iprop(⌜v3rpc.auxOf r = v3rpc.auxOf r'⌝) $$ []
  · iapply streamAuxIs_agree; isplit
    · iexact Hax
    · iexact Hax'
  obtain ⟨hreg, -, -, -⟩ := v3rpc.auxOf_inj He
  irevert Hreg; rw [← hreg]; iintro #Hreg
  irevert Hl Ho; rw [← hrW]; iintro #Hl #Ho
  imod recvEvents r j m n x ⟨rg, lo, k⟩ hsrc hX1 $$ [Hl Ho Hmv Hreg]
    with ⟨%pre, %Ls, %L, %d, #HLs, -, #HL, %H⟩
  · iframe #
  ihave %HLD : ⌜Ls = Dm⌝ $$ []
  · iunfold v3rpc.downLbW at Hdn
    irevert HLs; rw [hrs]; iintro #HLs
    ihave %Hcmp := mono_list_lb_valid _ Ls Dm $$ HLs Hdn
    ipureintro
    exact eq_of_comparable Hcmp (by rw [hj]; exact H.1)
  subst HLD
  imodintro
  iexists pre, L, d
  isplitr
  · iexact HL
  ipureintro
  exact ⟨H.2.2.2.2, H.2.2.2.1, H.2.2.1⟩

/-- **Before dispatching an mvcc response to its registered substream** (the `n`-th the run `r`
received, `x`, of the id `x.id`; `recvc` producer at `sent`, cursors `C`): the response's events,
the header for `dispatchEvent`, the content of the response for the substream (`recvElem`), the
cursors extended by the new one and the substream's state after it (the stop flag, or the cursor
of the events received with this response). -/
theorem reg_pre (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B)
    (Dm : List v3rpc.WatchRespM) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs)
    (j : Nat) (m : v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp)
    (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc) (C : List w64)
    (h : Loc) (sl : GoSlice) (ps : List Loc) (kvs : List Loc)
    (hsrc : m.src = some (n, x)) (hev : m.evs = x.evs)
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false)
    (hps : ps.length = x.evs.length) (hkvl : kvs.length = x.evs.length)
    (hok : wsReqOk V.pfx P) (hpfx : V.pfx ≠ []) (hhn : h ≠ null)
    (hj : Dm.length = j) (hcplP : P.γ.cpl = cplOf P) (hlive : v3rpc.idLive Dm x.id)
    (hX1 : x.id ≠ W64 (-1)) (hkst : P.kv.st = V.kst) :
    srvKVFacts V ∗ wsAu P ∗ srvWLaws V.W ∗ v3rpc.srvOnce V.W ∗ watchLaws V ∗
      startOk V B.srr B.rr ∗ v3rpc.downLbW γs Dm ∗ cur2St V γs Dm P B x.id rg lo sent ∗
      streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗
      regFacts V γs Dm P B x.id rg lo ∗ sl ↦*□ ps ∗
      ([∗list] y ∈ ps.zip x.evs, mvcc.evIs (GF := GF) y.1 y.2) ∗
      eventsAt sl (List.zipWith evModelOf x.evs kvs) ∗
      monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ (∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P B Dm x.id rg lo hi) ∗ psAt P sent.length) ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ m.hdr.revision ⊢
    |={⊤}=> ∃ (es : List EvModel) (C' C2 : List w64), eventsAt sl es ∗ ⌜es.length = m.evs.length⌝ ∗
      (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision) ∗ monoListAuthOwn P.γhi 1 C' ∗
      (∀ wr : Loc, wr ↦□ wrOf m h sl -∗ recvElem V P sent.length wr) ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ (∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P B (Dm ++ [m]) x.id rg lo hi) ∗ psAt P (sent.length + 1)) ∗
      cur2Pend V γs (Dm ++ [m]) P B x.id rg lo sent C2 := by
  iintro ⟨#Hkf, #Hwa, #Hl, #Ho, #Hlaws, #Hso, #Hdn, Hc2, #Hax, #Hmv, #Hrf, #Hsl, #Hevs, #Hea, Hauth,
    Hst, Hrev⟩
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
    iexists List.zipWith evModelOf x.evs kvs, C, C2
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
  ihave #Hrf0 := Hrf
  iunfold regFacts at Hrf0
  icases Hrf0 with ⟨%Hcr, -, #Hrow⟩
  obtain ⟨hcr, hlor, hlo0⟩ := Hcr
  iunfold cursorOk at Hcur
  icases Hcur with ⟨%Hhi, #Hcut⟩
  -- the events received, from the snapshot
  ihave Hevd : iprop(|={⊤}=> ∃ (pre : List mvcc.api.WResp) (L : mvcc.Log) (d : Nat),
      □ (⌜x.evs ≠ []⌝ -∗ □ V.W.histLb L) ∗
      ⌜x.evs ≠ [] → (v3rpc.sentEvsOf Dm x.id ++ [x] =
          ((pre ++ [x]).filter (fun y => decide (y.id = x.id))).filter
            (fun y => decide (y.evs ≠ []))) ∧
        mvcc.api.recvEvs (pre ++ [x]) x.id = mvcc.watchEvents L rg lo d ∧ d ≤ L.length⌝) $$ []
  · by_cases hne : x.evs = []
    · imodintro
      iexists [], [], 0
      isplitr
      · iintro !> %h'; exact absurd hne h'
      ipureintro; intro h'; exact absurd hne h'
    · imod reg_events V γs P B Dm r hrW hrs j m n x rg lo hsrc hX1 hj $$ [] with
        ⟨%pre, %L, %d, #HL, %HLd⟩
      · iframe #
      imodintro
      iexists pre, L, d
      isplitr
      · iintro !> %-; iexact HL
      ipureintro; intro hne'; exact ⟨HLd.1 hne', HLd.2.1, HLd.2.2⟩
  imod Hevd with ⟨%pre, %L, %d, #HLw, %HLd⟩
  ihave Hdc := dispatch_content V P B.rr B.srr B.hb Dm m n x pre x.id rg lo hi sl ps
      m.hdr.revision L d hsrc (fun _ => rfl) (fun hne => (HLd hne).1)
      (fun hne => ⟨(HLd hne).2.1, (HLd hne).2.2⟩) hps hok hpfx hcr hB.1 hlor hB.2.1 Hhi $$ []
  · iframe Hl HLw Hcut Hsl Hevs
  imod Hdc with ⟨%es, #Hes, %Hesl, #Hrok, %Hhi', #Hcut', %kvs', %Hkvs, #Hkv⟩
  -- (D25) the position marked, the resume fact
  imod psAt_mark P sent.length $$ Hps with ⟨Hps, #Hns⟩
  ihave #Hrf0 : resumeF V P ⟨es, W64 0, false, false, m.hdr.revision⟩ $$ []
  · iapply resumeF_holds
  have hv : ¬ watchErr (wrOf m h sl) := by
    unfold watchErr wrOf; simp [hfl.1, hfl.2.1]
  ihave ⟨%pre1, %Ls1, %σ1, %S1, %Hm1, -, -, -, -, -⟩ := mvccOk_at r j m n x hsrc $$ Hmv
  have hxc : x.compactRev = W64 0 := by
    have := congrArg v3rpc.WatchRespM.compactRev Hm1.1
    simp only [v3rpc.mvccResp] at this; rw [← this]; exact hfl.1
  ihave Hcmp : iprop(|={⊤}=> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P B x.id rg lo sent C2 ∗
      (dghostVar P.γx DFrac.discard true ∨ recvCmpl V P (sent.length : Int) (wrOf m h sl)
        ⟨es, W64 0, false, false, m.hdr.revision⟩)) $$ [Hc2]
  · by_cases hne : x.evs = []
    · -- an event-less response of the substream's own id: a progress notification
      have hes0 : es = [] := by
        rw [← List.length_eq_zero_iff, Hesl, hne]; rfl
      imod regCov V γs P B Dm r hrW hrs j m n x x.id rg lo hsrc hne hxc hX1 hj hlive (Or.inl rfl)
        $$ [] with (#Hwc | ⟨%Hm1, -⟩)
      · iframe #
      rotate_left
      · exact absurd Hm1 hX1
      iapply cmpl_step V γs Dm m P B x.id rg lo sent (wrOf m h sl) _
        iprop(streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗ v3rpc.downLbW γs Dm ∗
          regFacts V γs Dm P B x.id rg lo ∗ progCovd r Dm n x x.id rg lo ∗ srvWLaws V.W) hkst
        (fun hc c2 => by
          iintro ⟨#Hc, #Hq1, #Hq2, #Hq3, #Hq4, #Hq5, #Hq6⟩
          iapply prog_cmpl V γs P B hB Dm r hrW hrs j m n x x.id rg lo c2 (wrOf m h sl) _ hj hsrc
            hne hlive hX1 (Or.inl rfl) hok hcplP hc hv ⟨hes0, rfl, rfl, rfl, rfl⟩ hfl.1
          iframe #)
      iframe Hc2
      iframe #
    · -- events: the watcher's, the watch events of a certified log
      obtain ⟨hfilt, h2, hd⟩ := HLd hne
      rw [evs_after Dm x.id pre x hfilt] at h2
      have hsnoc : evsOf (Dm ++ [m]) x.id = evsOf Dm x.id ++ x.evs := by
        unfold evsOf
        rw [sentEvsOf_snoc, hsrc]
        simp [hne]
      ihave #HL : □ V.W.histLb L $$ []
      · iapply HLw; ipureintro; exact hne
      iapply cmpl_step V γs Dm m P B x.id rg lo sent (wrOf m h sl) _
        iprop(□ V.W.histLb L ∗ srvWLaws V.W ∗
          □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜x.evs[k]? = some ev⌝ → ⌜kvs'[k]? = some kv⌝ →
            mvcc.kvPtrFixed kv ev.kv)) hkst
        (fun hc c2 => by
          iintro ⟨#Hc, #Hq1, #Hq2, #Hq3⟩
          have hcov := cpl_cov V P B x.id rg hok hcplP hc hB hcr
          imodintro
          iapply cmpl_events V γs B.rr Dm m x.id rg lo c2 P.o hcov L d x.evs kvs' Hkvs.2 hne
            hsnoc h2 (Or.inl hd) (wrOf m h sl) _ Hkvs.1 hv
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
  ihave #Hi1 := monoListIdxOwn_get (γ := P.γhi) (sent.length + 1)
    ((es.getLast?.map EvModel.rev).getD hi) hC1 $$ Hlb
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
    iframe Hwr Hes Hwo Hi0 Hi1 Hrok Hcm' Hns Hrf0
    iintro !> -
    iexact Hrow
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

/-- **An mvcc response's compaction revision is the cluster's permit** (C3's watch side,
2026-11-02; strict M1: at most the snapshot's permitted compaction revision, `compactResp`, which
the member's KV facts make the cluster's, `srvKVFacts_cmp`, downward closed). -/
theorem cmpOkOf_of_mvccOk (V : WEnv GF) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (j : Nat)
    (m : v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp) (hsrc : m.src = some (n, x)) :
    srvKVFacts V ∗ □ v3rpc.mvccOk r j m ⊢ cmpOkOf V.kv m.compactRev := by
  iintro ⟨#Hkf, #Hmv⟩
  ihave ⟨%pre1, %Ls1, %σ1, %S1, %Hm1, -, -, -, -, -⟩ := mvccOk_at r j m n x hsrc $$ Hmv
  have hmc : m.compactRev = x.compactRev := by
    have := congrArg v3rpc.WatchRespM.compactRev Hm1.1
    simp only [v3rpc.mvccResp] at this; exact this
  rw [hmc]
  by_cases h0 : x.compactRev = W64 0
  · iunfold cmpOkOf; ileft; ipureintro; exact h0
  ihave ⟨%c, Hc, %Hcx⟩ := compactResp r j m n x hsrc h0 $$ Hmv
  irevert Hc; rw [hrW]; iintro #Hc
  icases srvKVFacts_cmp V c $$ [$Hkf $Hc] with (%hm1 | #Hk)
  · exfalso; omega
  iunfold cmpOkOf; iright
  iapply kvCmpPermit_le V.kv (sint.Z x.compactRev) c Hcx.2.2.2.1 Hcx.2.2.2.2 $$ Hk

/-- **Before dispatching a compaction response to its registered substream** (watches across a
compaction, D6, 2026-11-01): as `reg_pre`, for mvcc's response to a watch behind the compaction
revision (canceled, no events, at the header revision `0`): an error for the substream, its
cursors kept. -/
theorem reg_pre_cmp (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B)
    (Dm : List v3rpc.WatchRespM) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs)
    (j : Nat) (m : v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp)
    (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc) (C : List w64)
    (h : Loc) (sl : GoSlice) (ps : List Loc) (kvs : List Loc)
    (hsrc : m.src = some (n, x)) (hev : m.evs = x.evs)
    (hfl : m.compactRev ≠ W64 0 ∧ m.canceled = true ∧ m.created = false ∧ m.evs = [] ∧
      m.hdr.revision = W64 0)
    (hps : ps.length = x.evs.length) (hkvl : kvs.length = x.evs.length)
    (hok : wsReqOk V.pfx P) (hpfx : V.pfx ≠ []) (hhn : h ≠ null)
    (hj : Dm.length = j) (hcplP : P.γ.cpl = cplOf P) (hlive : v3rpc.idLive Dm x.id)
    (hX1 : x.id ≠ W64 (-1)) (hkst : P.kv.st = V.kst) :
    srvKVFacts V ∗ wsAu P ∗ srvWLaws V.W ∗ v3rpc.srvOnce V.W ∗ watchLaws V ∗
      startOk V B.srr B.rr ∗ v3rpc.downLbW γs Dm ∗ cur2St V γs Dm P B x.id rg lo sent ∗
      streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗
      regFacts V γs Dm P B x.id rg lo ∗ sl ↦*□ ps ∗
      ([∗list] y ∈ ps.zip x.evs, mvcc.evIs (GF := GF) y.1 y.2) ∗
      eventsAt sl (List.zipWith evModelOf x.evs kvs) ∗
      monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ (∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P B Dm x.id rg lo hi) ∗ psAt P sent.length) ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ m.hdr.revision ⊢
    |={⊤}=> ∃ (es : List EvModel) (C' C2 : List w64), eventsAt sl es ∗ ⌜es.length = m.evs.length⌝ ∗
      (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision) ∗ monoListAuthOwn P.γhi 1 C' ∗
      (∀ wr : Loc, wr ↦□ wrOf m h sl -∗ recvElem V P sent.length wr) ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ (∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P B (Dm ++ [m]) x.id rg lo hi) ∗ psAt P (sent.length + 1)) ∗
      cur2Pend V γs (Dm ++ [m]) P B x.id rg lo sent C2 := by
  iintro ⟨#Hkf, #Hwa, #Hl, #Ho, #Hlaws, #Hso, #Hdn, Hc2, #Hax, #Hmv, #Hrf, #Hsl, #Hevs, #Hea, Hauth,
    Hst, Hrev⟩
  -- (C3's watch side) the response's compaction revision is the cluster's permit
  ihave #HcmpOk := cmpOkOf_of_mvccOk V r hrW j m n x hsrc $$ [Hkf Hmv]
  · iframe #
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
    iexists List.zipWith evModelOf x.evs kvs, C, C2
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
  -- the substream runs: the response's content (none)
  ihave #Hrf0 := Hrf
  iunfold regFacts at Hrf0
  icases Hrf0 with ⟨%Hcr, -, #Hrow⟩
  obtain ⟨hcr, hlor, hlo0⟩ := Hcr
  iunfold cursorOk at Hcur
  icases Hcur with ⟨%Hhi, #Hcut⟩
  have hρe : x.evs = [] := by rw [← hev]; exact hfl.2.2.2.1
  ihave Hdc := dispatch_content V P B.rr B.srr B.hb Dm m n x [] x.id rg lo hi sl ps
      m.hdr.revision [] 0 hsrc (fun _ => rfl) (fun hne => absurd hρe hne)
      (fun hne => absurd hρe hne) hps hok hpfx hcr hB.1 hlor hB.2.1 Hhi $$ []
  · iframe Hl Hcut Hsl Hevs
    iintro %hne; exact absurd hρe hne
  imod Hdc with ⟨%es, #Hes, %Hesl, #Hrok, %Hhi', #Hcut', %kvs', %Hkvs, #Hkv⟩
  -- (D25) the position marked, the resume fact's server side
  imod psAt_mark P sent.length $$ Hps with ⟨Hps, #Hns⟩
  have hes0 : es = [] := by rw [← List.length_eq_zero_iff, Hesl, hρe]; rfl
  -- (watches across a compaction) a compaction response: an error, the cursor kept
  have hv : watchErr (wrOf m h sl) := by
    unfold watchErr wrOf; right; left; exact hfl.1
  have hevs : evsOf (Dm ++ [m]) x.id = evsOf Dm x.id := by
    unfold evsOf
    rw [sentEvsOf_snoc, hsrc]
    simp [hρe]
  ihave Hcmp : iprop(|={⊤}=> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P B x.id rg lo sent C2 ∗
      (dghostVar P.γx DFrac.discard true ∨ recvCmpl V P (sent.length : Int) (wrOf m h sl)
        ⟨es, m.compactRev, true, false, m.hdr.revision⟩)) $$ [Hc2]
  · iapply cmpl_step V γs Dm m P B x.id rg lo sent (wrOf m h sl) _ iprop(True) hkst
      (fun _ c2 => by
        iintro ⟨#Hc, -⟩
        imodintro
        iexists c2
        isplitr
        · iunfold rawRespOk; ileft
          isplitr
          · ipureintro; exact ⟨hv, rfl⟩
          simp only [wrOf]; iapply statusErrOk_nil
        iapply cur2Ok_mono V γs B.rr x.id rg lo c2 hevs (List.prefix_append _ _) $$ Hc)
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
  ihave #Hi1 := monoListIdxOwn_get (γ := P.γhi) (sent.length + 1)
    ((es.getLast?.map EvModel.rev).getD hi) hC1 $$ Hlb
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
    unfold recvElem
    ileft
    iexists wrOf m h sl, ⟨es, m.compactRev, true, false, m.hdr.revision⟩, hi,
      ((es.getLast?.map EvModel.rev).getD hi)
    simp only [wrOf, Int.toNat_natCast, Bool.false_eq_true, ↓reduceIte]
    iframe Hwr Hes Hi0 Hi1 Hcm' Hns
    isplitr
    · ipureintro
      simp [hhn, hfl.2.1, hfl.2.2.1, hfl.2.2.2.2, hes0, respKindOk]; exact hfl.1
    isplitl [Hwo]
    · irevert Hwo
      unfold watchHdrOwn; simp only [hes0, ↓reduceIte]
      iintro Hwo; iexact Hwo
    isplitr
    · ipureintro; simp [dispOk, EvRevSorted, hes0]
    isplitr
    · iapply resumeF_holds
    isplitr
    · iintro !> %h'; exact absurd hes0 h'
    iexact HcmpOk
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

/-- **Before dispatching an mvcc response to its registered substream**, either kind (`reg_pre`,
`reg_pre_cmp`). -/
theorem reg_pre_any (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B)
    (Dm : List v3rpc.WatchRespM) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs)
    (j : Nat) (m : v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp)
    (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc) (C : List w64)
    (h : Loc) (sl : GoSlice) (ps : List Loc) (kvs : List Loc)
    (hsrc : m.src = some (n, x)) (hev : m.evs = x.evs)
    (hfl : m.created = false ∧ ((m.compactRev = W64 0 ∧ m.canceled = false) ∨
      (m.compactRev ≠ W64 0 ∧ m.canceled = true ∧ m.evs = [] ∧ m.hdr.revision = W64 0)))
    (hps : ps.length = x.evs.length) (hkvl : kvs.length = x.evs.length)
    (hok : wsReqOk V.pfx P) (hpfx : V.pfx ≠ []) (hhn : h ≠ null)
    (hj : Dm.length = j) (hcplP : P.γ.cpl = cplOf P) (hlive : v3rpc.idLive Dm x.id)
    (hX1 : x.id ≠ W64 (-1)) (hkst : P.kv.st = V.kst) :
    srvKVFacts V ∗ wsAu P ∗ srvWLaws V.W ∗ v3rpc.srvOnce V.W ∗ watchLaws V ∗
      startOk V B.srr B.rr ∗ v3rpc.downLbW γs Dm ∗ cur2St V γs Dm P B x.id rg lo sent ∗
      streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗
      regFacts V γs Dm P B x.id rg lo ∗ sl ↦*□ ps ∗
      ([∗list] y ∈ ps.zip x.evs, mvcc.evIs (GF := GF) y.1 y.2) ∗
      eventsAt sl (List.zipWith evModelOf x.evs kvs) ∗
      monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ (∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P B Dm x.id rg lo hi) ∗ psAt P sent.length) ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ m.hdr.revision ⊢
    |={⊤}=> ∃ (es : List EvModel) (C' C2 : List w64), eventsAt sl es ∗ ⌜es.length = m.evs.length⌝ ∗
      (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision) ∗ monoListAuthOwn P.γhi 1 C' ∗
      (∀ wr : Loc, wr ↦□ wrOf m h sl -∗ recvElem V P sent.length wr) ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ (∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P B (Dm ++ [m]) x.id rg lo hi) ∗ psAt P (sent.length + 1)) ∗
      cur2Pend V γs (Dm ++ [m]) P B x.id rg lo sent C2 := by
  rcases hfl with ⟨h3, ⟨h1, h2⟩ | hk⟩
  · exact reg_pre V γs P B hB Dm r hrW hrs j m n x rg lo sent C h sl ps kvs hsrc hev ⟨h1, h2, h3⟩
      hps hkvl hok hpfx hhn hj hcplP hlive hX1 hkst
  · exact reg_pre_cmp V γs P B hB Dm r hrW hrs j m n x rg lo sent C h sl ps kvs hsrc hev
      ⟨hk.1, hk.2.1, h3, hk.2.2.1, hk.2.2.2⟩ hps hkvl hok hpfx hhn hj hcplP hlive hX1 hkst

/-- **After dispatching to a registered substream**: its state over the new response, whether
the send succeeded or failed. -/
theorem reg_post (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (X : w64) (rg : mvcc.WatchRange) (lo : Nat)
    (sent : List Loc) (C' C2 : List w64) (b : Bool) (wr : Loc) (d : DnInfo GF) (γend : GName)
    (n : Nat) :
    regFacts V γs Dm P B X rg lo ∗ startOk V B.srr B.rr ∗ monoListAuthOwn P.γhi 1 C' ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ (∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P B (Dm ++ [m]) X rg lo hi) ∗ psAt P (sent.length + 1)) ∗
      cur2Pend V γs (Dm ++ [m]) P B X rg lo sent C2 ∗
      ((⌜b = true⌝ ∗ sendDone P sent wr d γend n) ∨ (⌜b = false⌝ ∗ sendFail V P sent wr d γend n)) ⊢
    wsRest V γs (Dm ++ [m]) P (.reg X) ∗ dnCap P d γend n := by
  iintro ⟨#Hrf, #HsoB, Hauth, Hst, Hpend, Hs⟩
  have HB := hB
  simp only [wsRest]
  unfold cur2Pend
  icases Hpend with ⟨Ha2, Hp2⟩
  ihave #Hrf' := regFacts_mono V γs P B X rg lo (List.prefix_append Dm [m]) $$ Hrf
  icases Hs with (⟨%-, Hd⟩ | ⟨%-, Hf⟩)
  · iunfold sendDone at Hd
    icases Hd with ⟨Hd, Hdc⟩
    iframe Hdc
    iexists B, rg, lo, sent ++ [wr], C'
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
    iexists B, rg, lo, sent, C'
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
by the same one, and the substream's state after it. Strict M1: the response the `nx`-th the run
`r` received, its coverage of the substream's watcher `progCovd` (or the substream stopped). -/
theorem bcast_pre (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (B : RegB) (hB : regBOk P B)
    (Dm : List v3rpc.WatchRespM) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs)
    (j : Nat) (m : v3rpc.WatchRespM) (nx : Nat) (x : mvcc.api.WResp) (X : w64)
    (rg : mvcc.WatchRange) (lo : Nat) (sent : List Loc) (C : List w64)
    (h : Loc) (sl : GoSlice) (hsrc : m.src = some (nx, x)) (hev : x.evs = [])
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false) (hhn : h ≠ null)
    (hj : Dm.length = j) (hok : wsReqOk V.pfx P) (hcplP : P.γ.cpl = cplOf P)
    (hlive : v3rpc.idLive Dm X) (hX1 : X ≠ W64 (-1)) (hid : x.id = W64 (-1))
    (hkst : P.kv.st = V.kst) :
    srvKVFacts V ∗ wsAu P ∗
    hdrAt h m.hdr.revision ∗ eventsAt sl [] ∗ monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ (∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P B Dm X rg lo hi) ∗ psAt P sent.length) ∗
      cur2St V γs Dm P B X rg lo sent ∗
      (progCovd r Dm nx x X rg lo ∨ dghostVar P.γx DFrac.discard true) ∗
      streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗ v3rpc.downLbW γs Dm ∗
      regFacts V γs Dm P B X rg lo ∗ startOk V B.srr B.rr ∗ srvWLaws V.W ∗ watchLaws V ⊢
    |={⊤}=> ∃ C' C2 : List w64, monoListAuthOwn P.γhi 1 C' ∗
      (∀ wr : Loc, wr ↦□ wrOf m h sl -∗ recvElem V P sent.length wr) ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ (∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P B (Dm ++ [m]) X rg lo hi) ∗ psAt P (sent.length + 1)) ∗
      cur2Pend V γs (Dm ++ [m]) P B X rg lo sent C2 := by
  iintro ⟨#Hkf, #Hwa, #Hha, #Hea, Hauth, Hst, Hc2, #Hmem, #Hax, #Hmv, #Hdn, #Hrf, #Hso, #Hl,
    #Hlaws⟩
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
  ihave Hcmp : iprop(|={⊤}=> ∃ C2 : List w64, cur2Pend V γs (Dm ++ [m]) P B X rg lo sent C2 ∗
      (dghostVar P.γx DFrac.discard true ∨ recvCmpl V P (sent.length : Int) (wrOf m h sl)
        ⟨[], W64 0, false, false, m.hdr.revision⟩)) $$ [Hc2]
  · icases Hmem with (#Hwc | #Hx2)
    · iapply cmpl_step V γs Dm m P B X rg lo sent (wrOf m h sl) _
        iprop(streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗ v3rpc.downLbW γs Dm ∗
          regFacts V γs Dm P B X rg lo ∗ progCovd r Dm nx x X rg lo ∗ srvWLaws V.W) hkst
        (fun hc c2 => by
          iintro ⟨#Hc, #Hq1, #Hq2, #Hq3, #Hq4, #Hq5, #Hq6⟩
          iapply prog_cmpl V γs P B hB Dm r hrW hrs j m nx x X rg lo c2 (wrOf m h sl) _ hj hsrc
            hev hlive hX1 (Or.inr hid) hok hcplP hc hv ⟨rfl, rfl, rfl, rfl, rfl⟩ hfl.1
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
  -- (D25) the position marked
  imod psAt_mark P sent.length $$ Hps with ⟨Hps, #Hns⟩
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
  have hevs : evsSoFar (Dm ++ [m]) X = evsSoFar Dm X := by
    unfold evsSoFar evsOf
    rw [sentEvsOf_snoc, hsrc]
    simp [hev]
  imodintro
  iexists C ++ [hi], C2
  iframe Hauth Hpend
  isplitr
  · iintro %wr #Hwr
    icases Hcm with (#Hx2 | #Hcm')
    · unfold recvElem; iright; iexact Hx2
    ihave #Hrf0 : resumeF V P ⟨[], W64 0, false, false, m.hdr.revision⟩ $$ []
    · iapply resumeF_holds
    iapply recvElem_of V P sent.length (by intro h0; exact Hsne (List.length_eq_zero_iff.1 h0)) m h
      sl [] hi hi wr hfl hhn
    iframe Hwr Hea Hi0 Hi1 Hcm' Hns Hrf0
    isplitr
    · simp only [watchHdrOwn, ↓reduceIte]; iexact Hha
    isplitr
    · ipureintro; simp [dispOk, EvRevSorted]
    iintro !> %hne
    exact absurd rfl hne
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
K2e-7d; strict M1: `progCovd`): for the substream `ws` at the id `X`, whatever its values. -/
def bcastCov (V : WEnv GF) (γs : StreamNames) (S : RunSt) (r : v3rpc.WRun GF) (nx : Nat)
    (x : mvcc.api.WResp) (X : w64) (ws : Loc) : IProp GF :=
  iprop(□ ∀ (P : WsPrm GF) (B : RegB) (rg : mvcc.WatchRange) (lo : Nat),
    ⌜P.ws = ws⌝ -∗ regFacts V γs S.Dm P B X rg lo -∗ noCancelOk S P (.reg X) -∗
      (progCovd r S.Dm nx x X rg lo ∨ dghostVar P.γx DFrac.discard true))

instance bcastCov_persistent (V : WEnv GF) (γs : StreamNames) (S : RunSt) (r : v3rpc.WRun GF)
    (nx : Nat) (x : mvcc.api.WResp) (X : w64) (ws : Loc) :
    Persistent (bcastCov V γs S r nx x X ws) := by
  unfold bcastCov; infer_instance

instance cancelQ_timeless (γs : StreamNames) (id : w64) : Timeless (v3rpc.cancelQ (GF := GF) γs id) := by
  unfold v3rpc.cancelQ v3rpc.upAtW; infer_instance

/-- **One id's registered watcher**: two `regFacts` of one id name one range and first revision
(the run's registry entry, by the stream's auxiliary name). -/
theorem regFacts_agree (V : WEnv GF) (γs : StreamNames) (Dm Dm' : List v3rpc.WatchRespM)
    (P P' : WsPrm GF) (B B' : RegB) (X : w64) (rg rg' : mvcc.WatchRange) (lo lo' : Nat) :
    regFacts V γs Dm P B X rg lo ∗ regFacts V γs Dm' P' B' X rg' lo' ⊢ ⌜rg = rg' ∧ lo = lo'⌝ := by
  iintro ⟨#H1, #H2⟩
  iunfold regFacts at H1 H2
  iunfold regSnap at H1 H2
  icases H1 with ⟨-, ⟨%r1, %k1, %l1, %L1, #Ha1, #Hr1, -, -⟩, -⟩
  icases H2 with ⟨-, ⟨%r2, %k2, %l2, %L2, #Ha2, #Hr2, -, -⟩, -⟩
  ihave %He : iprop(⌜v3rpc.auxOf r1 = v3rpc.auxOf r2⌝) $$ []
  · iapply streamAuxIs_agree; isplit
    · iexact Ha1
    · iexact Ha2
  obtain ⟨hreg, -, -, -⟩ := v3rpc.auxOf_inj He
  irevert Hr2; rw [← hreg]; iintro #Hr2
  iunfold v3rpc.regIs at Hr1 Hr2
  ihave %Hi := ghostMapElem_agree _ _ _ _ _ _ $$ Hr1 Hr2
  ipureintro
  simp only [v3rpc.RegInfo.mk.injEq] at Hi
  exact ⟨Hi.1, Hi.2.1⟩

/-- **(a) A registered substream's watcher, at a broadcast**: covered for every value of the
substream with its id's `regFacts`, or the client asked to cancel the id (`regCov`, its range and
first revision the registry's, `regFacts_agree`). -/
theorem bcast_regPair (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S : RunSt}
    (X : w64) (ws : Loc) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs) (j : Nat)
    (m : v3rpc.WatchRespM) (nx : Nat) (x : mvcc.api.WResp) (hsrc : m.src = some (nx, x))
    (hxe : x.evs = []) (hxc : x.compactRev = W64 0) (hid : x.id = W64 (-1))
    (hj : S.Dm.length = j) (hM : S.M !! X = some ws)
    (hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y) :
    srvWLaws V.W ∗ v3rpc.srvOnce V.W ∗ streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗
      v3rpc.downLbW γs S.Dm ∗ wsElem V G n γs S ws ⊢
      |={⊤}=> wsElem V G n γs S ws ∗ □ (v3rpc.cancelQ γs X ∨
        □ ∀ (P : WsPrm GF) (B : RegB) (rg : mvcc.WatchRange) (lo : Nat), ⌜P.ws = ws⌝ -∗
          regFacts V γs S.Dm P B X rg lo -∗ progCovd r S.Dm nx x X rg lo) := by
  iintro ⟨#Hl, #Ho, #Hax, #Hmv, #Hdn, Hw⟩
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph, %Hkey⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  have hph0 : ph = WPh.reg X := by
    cases ph with
    | queued si => exact absurd hM (Hph.1 X)
    | orphan => exact absurd hM (Hph.1 X)
    | closed => exact absurd hM (Hph.1 X)
    | closedRun Y => exact absurd hM (Hph.1.2.1 X)
    | reg Y => rw [hinj Y X ws Hph.1 hM]
  subst hph0
  iunfold wsRest at Hrest
  icases Hrest with ⟨%B, %rg, %lo, %sent, %C, %HB, #HsoB, #Hrg, Hprod, Hauth, Hst, Hc2⟩
  imod regCov V γs P B S.Dm r hrW hrs j m nx x X rg lo hsrc hxe hxc Hph.2.2.2.2.1 hj
    Hph.2.2.2.2.2.2.2 (Or.inr hid) $$ [] with (#Hc | ⟨-, #Hq⟩)
  · iframe #
  all_goals
    imodintro
    isplitl [Hid Hprod Hauth Hst Hc2 Hlife]
    · iexists P, .reg X
      iframe HP Hid Hnc Hlife
      isplitr
      · ipureintro; exact ⟨HPws, Hph, Hkey⟩
      simp only [wsRest]
      iexists B, rg, lo, sent, C
      isplitr
      · ipureintro; exact HB
      iframe HsoB
      iframe Hrg Hprod Hauth Hst Hc2
  · iintro !>
    iright
    iintro !> %P' %B' %rg' %lo' %- #Hrf'
    ihave %Hag := regFacts_agree V γs S.Dm S.Dm P P' B B' X rg rg' lo lo' $$ [$Hrg $Hrf']
    obtain ⟨rfl, rfl⟩ := Hag
    iexact Hc
  · iintro !>
    ileft; iexact Hq

/-- **(b) Every registered substream's watcher, at a broadcast**, over a list of them: the client's
cancel requests are among its sent requests (`cliSendTok`). -/
theorem cov_cancel (γs : StreamNames) (L : List v3rpc.WatchReqM) (Q : w64 → Loc → IProp GF)
    [∀ X ws, Persistent (Q X ws)] :
    ∀ kvs : List (w64 × Loc), cliSendTok (GF := GF) (Req := v3rpc.pbWatchRequest) γs L ∗
      □ ([∗list] kv ∈ kvs, v3rpc.cancelQ γs kv.1 ∨ Q kv.1 kv.2) ⊢
      cliSendTok (Req := v3rpc.pbWatchRequest) γs L ∗
        □ ([∗list] kv ∈ kvs, ⌜∃ i : Nat, L[i]? = some (.cancel kv.1)⌝ ∨ Q kv.1 kv.2)
  | [] => by
    iintro ⟨Ht, -⟩
    iframe Ht
    iintro !>; iapply BigSepL.bigSepL_nil.2; itrivial
  | kv :: kvs => by
    iintro ⟨Ht, #H⟩
    ihave ⟨#Hh, #Ht'⟩ := BigSepL.bigSepL_cons.1 $$ H
    ihave ⟨Ht, #Hih⟩ := cov_cancel γs L Q kvs $$ [Ht]
    · iframe Ht Ht'
    icases Hh with (#Hq | #Hq)
    · iunfold v3rpc.cancelQ at Hq
      icases Hq with ⟨%i, #Hu⟩
      icases sendTok_lookup γs L i (.cancel kv.1) $$ [Ht Hu] with ⟨Ht, %HLi⟩
      · iframe Ht Hu
      iframe Ht
      iintro !>
      iapply BigSepL.bigSepL_cons.2
      iframe Hih
      ileft; ipureintro; exact ⟨i, HLi⟩
    · iframe Ht
      iintro !>
      iapply BigSepL.bigSepL_cons.2
      iframe Hih
      iright; iexact Hq

/-- **A broadcast covers every registered substream's watcher, unless it stopped** (K2e-7d):
(a) and (b) above, for the substreams of `substreams` (`S.M`); a watcher not covered was
cancelled at the client's request, which `run` makes only after a dispatch failed, which stopped
it (`noCancelOk`). -/
theorem bcast_covAll (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S : RunSt}
    (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs) (j : Nat) (m : v3rpc.WatchRespM)
    (nx : Nat) (x : mvcc.api.WResp) (hsrc : m.src = some (nx, x)) (hxe : x.evs = [])
    (hxc : x.compactRev = W64 0) (hid : x.id = W64 (-1)) (hj : S.Dm.length = j)
    (hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y) :
    srvWLaws V.W ∗ v3rpc.srvOnce V.W ∗ streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗
      v3rpc.downLbW γs S.Dm ∗
      cliSendTok (Req := v3rpc.pbWatchRequest) γs S.L ∗ ([∗map] _X ↦ ws ∈ S.M, wsElem V G n γs S ws) ⊢
      |={⊤}=> cliSendTok (Req := v3rpc.pbWatchRequest) γs S.L ∗
        ([∗map] _X ↦ ws ∈ S.M, wsElem V G n γs S ws) ∗
        □ (∀ (X : w64) (ws : Loc), ⌜S.M !! X = some ws⌝ -∗ bcastCov V γs S r nx x X ws) := by
  iintro ⟨#Hl, #Ho, #Hax, #Hmv, #Hdn, Ht, Hm⟩
  ihave Hm2 := BigSepM.bigSepM_impl (Ψ := fun X ws => iprop(|={⊤}=> wsElem V G n γs S ws ∗
      □ (v3rpc.cancelQ γs X ∨ □ ∀ (P : WsPrm GF) (B : RegB) (rg : mvcc.WatchRange) (lo : Nat),
        ⌜P.ws = ws⌝ -∗ regFacts V γs S.Dm P B X rg lo -∗ progCovd r S.Dm nx x X rg lo)))
      $$ Hm []
  · iintro !> %X %ws %hX Hw
    iapply bcast_regPair V G n γs X ws r hrW hrs j m nx x hsrc hxe hxc hid hj hX hinj
    iframe Hl Ho Hax Hmv Hdn Hw
  imod (BigSepM.bigSepM_fupd ⊤ _ _) $$ Hm2 with Hm2
  rw [BigSepM.bigSepM_sep_eq]
  icases Hm2 with ⟨Hm, #Hps⟩
  ihave #Hps' : □ ([∗map] X ↦ ws ∈ S.M, v3rpc.cancelQ γs X ∨
      □ ∀ (P : WsPrm GF) (B : RegB) (rg : mvcc.WatchRange) (lo : Nat),
        ⌜P.ws = ws⌝ -∗ regFacts V γs S.Dm P B X rg lo -∗ progCovd r S.Dm nx x X rg lo) $$ []
  · iintro !>
    iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by iintro #H; iexact H)) $$ Hps
  ihave #Hl2 := (BigSepM.bigSepM_toList (Φ := fun X ws => iprop(v3rpc.cancelQ (GF := GF) γs X ∨
      □ ∀ (P : WsPrm GF) (B : RegB) (rg : mvcc.WatchRange) (lo : Nat),
        ⌜P.ws = ws⌝ -∗ regFacts V γs S.Dm P B X rg lo -∗ progCovd r S.Dm nx x X rg lo))
      (m := S.M)).1 $$ Hps'
  ihave ⟨Ht, #Hcc⟩ := cov_cancel γs S.L (fun X ws => iprop(□ ∀ (P : WsPrm GF) (B : RegB)
      (rg : mvcc.WatchRange) (lo : Nat), ⌜P.ws = ws⌝ -∗ regFacts V γs S.Dm P B X rg lo -∗
        progCovd r S.Dm nx x X rg lo)) (Iris.Std.toList S.M) $$ [Ht]
  · iframe Ht Hl2
  imodintro
  iframe Ht Hm
  iintro !> %X %ws %hX
  unfold bcastCov
  iintro !> %P %B %rg %lo %HPws #Hrf #Hnc
  have hmem : (X, ws) ∈ Iris.Std.toList S.M := Iris.Std.toList_get.2 hX
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
  ihave #Hc := (BigSepL.bigSepL_lookup (Φ := fun _ (kv : w64 × Loc) =>
    iprop(⌜∃ i : Nat, S.L[i]? = some (.cancel kv.1)⌝ ∨ □ ∀ (P : WsPrm GF) (B : RegB)
      (rg : mvcc.WatchRange) (lo : Nat), ⌜P.ws = kv.2⌝ -∗ regFacts V γs S.Dm P B kv.1 rg lo -∗
        progCovd (GF := GF) r S.Dm nx x kv.1 rg lo)) hi) $$ Hcc
  icases Hc with (%Hcan | #Hc)
  · obtain ⟨i', hi'⟩ := Hcan
    unfold noCancelOk
    icases Hnc with (%Hn | #Hx)
    · exact absurd hi' (Hn i')
    iright; iexact Hx
  ileft
  iapply Hc $$ %P %B %rg %lo %HPws Hrf

/-- **A registered substream, for a broadcast** (unit W-K): its send capability for the progress
response (`sendCap`, its values and `recvc` history), and its element after the send, whether it
succeeded or failed; (K2e-7d) the second cursor over the response, with its coverage
(`bcastCov`) and what the server says of it. -/
theorem bcast_elem (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) {S S' : RunSt}
    (X : w64) (ws : Loc) (r : v3rpc.WRun GF) (hrW : r.W = V.W) (hrs : r.γs = γs)
    (j : Nat) (m : v3rpc.WatchRespM) (nx : Nat) (x : mvcc.api.WResp) (h : Loc) (sl : GoSlice)
    (hsrc : m.src = some (nx, x))
    (hev : x.evs = []) (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false)
    (hhn : h ≠ null) (hM : S.M !! X = some ws)
    (hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y)
    (hD : S'.Dm = S.Dm ++ [m]) (hph : ∀ ph, phOk S ws ph → phOk S' ws ph) (hLe : S'.L = S.L)
    (hj : S.Dm.length = j) (hid : x.id = W64 (-1)) :
    hdrAt h m.hdr.revision ∗ eventsAt sl [] ∗ bcastCov V γs S r nx x X ws ∗
      streamAuxIs γs (v3rpc.auxOf r) ∗ □ v3rpc.mvccOk r j m ∗ v3rpc.downLbW γs S.Dm ∗
      srvWLaws V.W ∗ watchLaws V ∗ srvKVFacts V ∗ wsElem V G n γs S ws ⊢
    |={⊤}=> ∃ a : WsPrm GF × List Loc × DnInfo GF, ⌜a.1.ws = ws⌝ ∗
      sendCap V a.1 a.2.1 (fun wr => iprop(wr ↦□ wrOf m h sl)) a.2.2 G.γend n ∗
      (∀ wr : Loc, (sendDone a.1 a.2.1 wr a.2.2 G.γend n ∨ sendFail V a.1 a.2.1 wr a.2.2 G.γend n) -∗
        wsElem V G n γs S' ws) := by
  iintro ⟨#Hha, #Hea, #Hbc, #Hax, #Hmv, #Hdn, #Hl, #Hlaws, #Hkf, Hw⟩
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph, %Hkey⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
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
  icases Hrest with ⟨%B, %rg, %lo, %sent, %C, %HB, #HsoB, #Hrg, Hprod, Hauth, Hst, Hc2⟩
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨-, -, -, -, -, -, %HPpure, #Hso, #Hwa, -, %Hkc, -⟩
  iunfold bcastCov at Hbc
  ihave #Hmem := Hbc $$ %P %B %rg %lo %HPws Hrg Hnc
  imod bcast_pre V γs P B HB S.Dm r hrW hrs j m nx x X rg lo sent C h sl hsrc hev hfl hhn hj
      HPpure.2.1 HPpure.2.2 Hph.2.2.2.2.2.2.2 Hph.2.2.2.2.1 hid Hkc.1
      $$ [$Hkf $Hwa $Hha $Hea $Hauth $Hst $Hc2 $Hmem $Hax $Hmv $Hdn $Hrg $HsoB $Hl $Hlaws]
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
    · iapply reg_post V γs P B HB S.Dm m X rg lo sent C' C2 true wr d G.γend n
      iframe Hrg HsoB Hauth Hst Hpend
      ileft; iframe Hd; ipureintro; rfl
    · iapply reg_post V γs P B HB S.Dm m X rg lo sent C' C2 false wr d G.γend n
      iframe Hrg HsoB Hauth Hst Hpend
      iright; iframe Hf; ipureintro; rfl
  iunfold dnCap at Hdc
  icases Hdc with ⟨Hdc, -⟩
  iexists P, .reg X
  isplitr
  · ipureintro; exact ⟨HPws, hph _ Hph, Hkey⟩
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
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph, %Hkey⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
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
  ipureintro; exact ⟨HPws, Hph, Hkey⟩

/-- **A new watcher's events so far are none** (pure; strict M1: by id): an mvcc response with
events of the id `X` received before was sent while `X` was live, so after a created response of
`X`, which would have registered it by then. -/
theorem evsSoFar_fresh {S : RunSt} {U : GMap Loc Unit} (X : w64) (hg : gOk S U) (hX : X ∉ S.regs)
    (hX1 : X ≠ W64 (-1)) : evsSoFar S.Dm X = [] := by
  by_cases hc : v3rpc.sentEvsOf S.Dm X = []
  · unfold evsSoFar evsOf; rw [hc]; rfl
  exfalso
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hc
  unfold v3rpc.sentEvsOf at hy
  simp only [List.mem_filter, decide_eq_true_eq] at hy
  obtain ⟨hym, hyX, -⟩ := hy
  obtain ⟨ρ, hρm, hρy⟩ := List.mem_map.1 hym
  obtain ⟨m', hm', hsrc'⟩ := List.mem_filterMap.1 hρm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm'
  have hl := hg.2.2.2.2.2.2.2.2.2.2.2.1 j m' ρ hj hsrc' (by rw [hρy, hyX]; exact hX1)
  rw [hρy, hyX] at hl
  obtain ⟨mc, hmc, hs, hw, hcr, hca⟩ := idLive_exists hl
  have := hg.2.2.2.2.2.2.2.2.2.2.2.2 mc (List.mem_of_mem_take hmc) hs hcr hca
  exact hX (hw ▸ this)

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
  · ipureintro; simp [hhn, h1, h2, h3, respKindOk]
  isplitr
  · unfold watchHdrOwn; simp only [↓reduceIte]; iexact Hha
  isplitr
  · ipureintro; simp [dispOk, EvRevSorted]
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
    ⟨G.γws, W64 0, apply.alarmChain false false false, [], G.γws, G.γws,
      ⟨G.γws, G.γws, G.γws, W64 0, G.γws, 0, G.γws, G.γws⟩, G.γws, false, G.γws, 0, .none⟩ (fun _ => iprop(True)) 0 0

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
  iintro ⟨%P, %ph, ⟨%HPws, %Hph, %Hkey⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
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
      icases Hrest with ⟨%B, %rg, %lo, %sent, %C, -, -, -, Hprod, -⟩
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
