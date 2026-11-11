/-
**The watch service's server** (`watch.go`; the watch slice's unit W-S, 2026-10-14): the facts and
the objects the proofs of `NewWatchServer`, `watchServer.Watch`, `recvLoop` and `sendLoop` share.
Lean-first (no Rocq counterpart); the design is in `notes/decisions.md`, "The watch stream's
server end: indexed queues, the delivery accounted by position".

**The package facts** (`watchVars`): what `watch.go` reads of package variables: `io.EOF`, the
`auth` and `mvcc` errors it compares with or reports (pointer leaves, `errVarLeaf`), the `rpctypes`
errors whose `Error()` it calls (`msgErrVar`) or returns, the metrics (`streamFailures`, the four
histograms: `Observe` returns), `traceutil.Tracer`, `context.Canceled`'s pointer error, the
progress interval's lock (`progressReportIntervalMu` guarding `progressReportInterval`, kept
between `10` and `2 ^ 62` nanoseconds: `intervalP`), and the contract of mvcc's names-only
`ReportEventReceived` (it returns). Assumptions about package initialization, as `v3rpcInit`.
(D19j, 2026-10-18: all but `io.EOF` are now `v3rpc`'s package facts, `watchPkgVars`,
`BaseWatch.lean` and `Base.lean`; `ReportEventReceived` is a callee of `sendLoop` with a
trust-boundary spec, `0 ≤ n`; `io.EOF` (`eofVar`) stayed a premise until Perennial's `io` fact
kept it, 2026-10-20: `eofVar_of_init`.)

**The server's contract** (`watchSrvOk s E tag`, persistent): `Term()`/`Leader()` return
(`raftStatusOk`), and its auth store (`isReqAuth`, A2's, and the apply package's `isAuthStore`,
both at the reader resource `E.RD`, the latter in the store's mode `E.authMode`), with auth on the
store's bound request side too (`isReqAuthBound`, the auth-mode merge, 2026-10-29), the mode's tag
`tag` (`auth.modeTag`, what a watcher's authorization names), and (G2, 2026-10-30) the server's
auth store at a reader's lower bound (`srvAuthLb`, what `isWatchPermitted` takes for a create's
bound: `True` with auth off, `srvAuthLb_off`). (The mvcc API migration, 2026-11-05: the watchable
store's internal contract `isWatchableStore`, its names `mvcc.WsNames` and its watch-token pool are
gone; the store is seen only through mvcc's API, at the server's side of the watch path `srvWOk`.)

**The server's side of the watch path** (`SrvW`, `srvPeek`, `srvWOk`, `srvOnce`; the draft
`notes/mvcc-api-clients/WatchSpecs.lean` §1, frozen): the store's handle and name, the namespace
of the server's invariant holding `mvccState`, the notified log's certified lower bound `histLb`
and the compaction revision's permit `crevOk`, with their laws: what the server gives.

**The watch server** (`isWatchServer p R`, persistent): `NewWatchServer`'s `*watchServer`, its
fields fixed (`WSrv`: the server, its environment, the watchable store, the auth mode's tag, the
cluster and member ids, the logger, the request budget).

**One run** (`WRun`, `swsIs sws r Up Dn st ci cd`, persistent; the draft's §3, §6): the run's
`serverWatchStream` `sws`, its fields (the gRPC stream, the mvcc watch stream `ws` (an interface
value: `NewWatchStream` does not say its dynamic type) with its API name `ι`, the control stream
`ctrl` (an SPSC channel from the receive loop to the send loop, `ctrlP`: each control response
answers a request), the three maps, `closec` (a broadcast
channel)), and the lock `mu` (a `sync.RWMutex` guarding the maps, `swsMu`: `prevKV` and `fragment`
empty, the restrictions' consequence); the run's invariant `wsInv` (the stream's state `wsState`,
the registry of watch ids `γreg` and their tokens `γtok`, the cancel facts, the close token `γcl`).

**The stream specification** (`watchDn`, `watchStreamSpec`; the draft's §4): every response the
server sends down at position `j` is either a control response answering an earlier request
(`ctrlOk`: a create request's `Created` response, canceled with watch id `-1` or registered with
its id and its registry entry; a cancel request's `Canceled` response; a created response after
every `-1` received before its watcher's stamp, `createdAfter`), or a response of the mvcc watch
stream (`mvccOk`): the `n`-th received, with the received list's lower bound and the send loop's
snapshot of it (`rcvSnap`: the API's watch guarantee `wsRecvOk` at a state and stream state of that
moment), and the bookkeeping of what was forwarded before it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream
public import Perennial.Proof.io.Base
public import Proof.errors.NewVar
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Proof.sync
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.DGhostVar
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc (watchServer serverWatchStream)

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The server `s` as an interface value (`apply.RaftStatusGetter`, `AuthGetter`). -/
abbrev srvIface (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s

/-- The field `f` of the run's `serverWatchStream`. -/
abbrev swsF (sws : Loc) (f : GoString) : Loc := structFieldRef serverWatchStream f sws

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The package facts -/

/-- **`io.EOF`** (persistent): a fixed `errors.New` error (a pointer leaf with an `Error()`, of a
type that implements `error`: `context.isTypedErr`). -/
def eofVar : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr _root_.Perennial.io.EOF ↦□ GoInterface.ok e ∗
    ⌜errLeaf e ∧ context.isTypedErr (GoInterface.ok e)⌝ ∗ errMsgOk e)

instance eofVar_persistent : Persistent (eofVar (GF := GF)) := by
  unfold eofVar errMsgOk; infer_instance

/-- **`io.EOF` from `io`'s package fact**: `io.isInit` keeps `EOF`'s value, an `errors.New("EOF")`
error (a fixed `*errorString` whose `Error()` returns, `io.eof_of_init`); the method-set facts of
`*errorString` (`ErrorStringLeaf`, and that it implements `error`) make it `eofVar`'s. -/
theorem eofVar_of_init [_root_.Perennial.io.Assumptions]
    :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢ eofVar := by
  iintro #Hpkg
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hpkg
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Hpt, #Hmsg⟩
  iunfold eofVar
  iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
  iframe Hpt
  isplitr
  · ipureintro
    exact ⟨errorString_errLeaf x, by simp only [context.isTypedErr]; go_type_set⟩
  iunfold errMsgOk
  iapply (errorMsg_triple (GF := GF)) $$ Hmsg

/-- **The package facts `watch.go` reads** (persistent; see the file header): `io.EOF`
(`eofVar`) and `v3rpc`'s package facts' part (`watchPkgVars`, D19j: `watchVars_of_init`). -/
def watchVars : IProp GF :=
  iprop(eofVar ∗ watchPkgVars)

instance watchVars_persistent : Persistent (watchVars (GF := GF)) := by
  unfold watchVars; infer_instance

/-- **`watchVars` from `v3rpc`'s package facts and `io.EOF`'s** (D19j, 2026-10-18). -/
theorem watchVars_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ eofVar ⊢
      watchVars := by
  iintro ⟨#Hpkg, #Heof⟩
  ihave Hi : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, -, -, -, #Hw, -⟩
  iunfold watchVars
  iframe Heof Hw

/-! ## The server's contract -/

/-- **The server's contract for the watch path** (persistent; see the file header). -/
def watchSrvOk (s : Loc) (E : apply.AEnv GF) (tag : GName) : IProp GF :=
  iprop(raftStatusOk s ∗
    (∃ (st : GoInterface) (cca : Bool) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc)
        (BT : mvcc.KBReal → IProp GF),
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st E.RD ∗
      □ (⌜E.authMode.isOn = true⌝ → isReqAuthBound st E.RD E.authMode) ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ apply.isAuthStore st Pk f BT E.RD E.authMode E.RW) ∗
    watchVars ∗ auth.modeTag tag E.authMode ∗
    -- (G2, 2026-10-30) the server's auth store at a reader's lower bound (what
    -- `isWatchPermitted` takes for a create's bound)
    srvAuthLb s E)

instance watchSrvOk_persistent (s : Loc) (E : apply.AEnv GF) (tag : GName) :
    Persistent (watchSrvOk s E tag) := by
  unfold watchSrvOk; infer_instance

/-- **The server's ids, as `NewWatchServer` reads them** (persistent): `Cluster().ID()` and
`MemberID()` return (two conjuncts of the KV server's contract `kvGetOk`, `srvIdsOk_of_kvGetOk`). -/
def srvIdsOk (s : Loc) : IProp GF :=
  iprop({{ True }} (App (Val (srvM s go!"Cluster")) (Val #()))
    {{ (c : GoInterface), RET #c; ∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
        {{ True }} (App (Val #(methods ci.ty go!"ID" ci.v)) (Val #()))
        {{ (id : w64), RET #id; True }} }} ∗
    {{ True }} (App (Val (srvM s go!"MemberID")) (Val #())) {{ (id : w64), RET #id; True }})

instance srvIdsOk_persistent (s : Loc) : Persistent (srvIdsOk (GF := GF) s) := by
  unfold srvIdsOk; infer_instance

theorem srvIdsOk_of_kvGetOk (s : Loc) (A : KVAns GF) : kvGetOk s A ⊢ srvIdsOk s := by
  iunfold kvGetOk
  iintro ⟨-, #HC, #HM, -⟩
  iunfold srvIdsOk
  iframe #

/-- **The watch server's values** (fixed by `NewWatchServer`): the server, its environment, the
watchable store, the auth mode's tag (W2 of the migration: in place of mvcc's `WsNames`, whose
`tag` it was), the cluster and member ids, the logger, the request budget. -/
structure WSrv (GF : BundledGFunctors) where
  s : Loc
  E : apply.AEnv GF
  wsl : Loc
  tag : GName
  cid : w64
  mid : w64
  lg : Loc
  mrb : w64

/-- **The `*watchServer` `p`** (persistent): its fields, the server's contract. -/
def isWatchServer (p : Loc) (R : WSrv GF) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ zapLoggerOk R.lg ∗
    structFieldRef watchServer go!"lg" p ↦□ R.lg ∗
    structFieldRef watchServer go!"clusterID" p ↦□ R.cid ∗
    structFieldRef watchServer go!"memberID" p ↦□ R.mid ∗
    structFieldRef watchServer go!"maxRequestBytes" p ↦□ R.mrb ∗
    structFieldRef watchServer go!"sg" p ↦□ srvIface R.s ∗
    structFieldRef watchServer go!"watchable" p ↦□ wsIface R.wsl ∗
    structFieldRef watchServer go!"ag" p ↦□ srvIface R.s ∗
    watchSrvOk R.s R.E R.tag)

instance isWatchServer_persistent (p : Loc) (R : WSrv GF) : Persistent (isWatchServer p R) := by
  unfold isWatchServer; infer_instance

/-! ## The client's restrictions -/

/-- **What the client's content of a request gives the server** (persistent; the draft's §5,
`upOk2`): the request is restricted (`watchReqOk`) and, for a create request, (G2's freeze,
2026-10-30) the client's bound on the auth store's published index in the server's mode `M`
(`authPubLbM M c.bound`, `watchUp`'s: what `recvLoop` checks the create at). (The mvcc API
migration, 2026-11-05: no watch token, which the API's `Watch` does not take, and no `watchNoDup`:
the API states the watch facts under `onceUpTo`, which v3rpc forwards, and the client discharges,
`srvOnce`.) -/
def upOk (M : auth.AuthMode) (Up : Nat → WatchReqM → IProp GF) : IProp GF :=
  iprop(□ ∀ (i : Nat) (m : WatchReqM), Up i m -∗ ⌜watchReqOk m⌝ ∗
    (match m with
     | .create c => □ auth.authPubLbM M c.bound
     | _ => iprop(True)))

instance upOk_persistent (M : auth.AuthMode) (Up : Nat → WatchReqM → IProp GF) :
    Persistent (upOk M Up) := by
  unfold upOk; infer_instance

/-- **The client's content of the watch method's requests** (unit W-W: what the client's `Send`
gives with each request, `Up` of the registered method): the request is restricted
(`watchReqOk`) and a create request comes with (G2, 2026-10-30) the client's bound on the auth
store's published index (`authPubLbM` of the create's ghost `bound`, at the server's mode: the
check is fresh at it). -/
def watchUp (R : WSrv GF) (_i : Nat) (m : WatchReqM) : IProp GF :=
  iprop(⌜watchReqOk m⌝ ∗
    (match m with
     | .create c => □ auth.authPubLbM R.E.authMode c.bound
     | _ => iprop(True)))

/-- The registered content meets the watch server's restrictions (`upOk`). -/
theorem upOk_watchUp (R : WSrv GF) : ⊢ upOk (GF := GF) R.E.authMode (watchUp R) := by
  unfold upOk
  iintro !> %i %m H
  unfold watchUp
  iexact H

/-- **What `sws.mu` guards** at the fraction `q`: the three maps, `prevKV` and `fragment` empty
(the client asks for neither: `watchReqOk`). -/
def swsMu (pm vm fm : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (PM VM FM : GMap w64 Bool),
    ownMap pm (DFrac.own q) PM ∗ ownMap vm (DFrac.own q) VM ∗ ownMap fm (DFrac.own q) FM ∗
    ⌜∀ id, VM !! id = none ∧ FM !! id = none⌝)

instance swsMu_fractional (pm vm fm : Loc) : Fractional (swsMu (GF := GF) pm vm fm) where
  fractional q1 q2 := by
    unfold swsMu
    constructor
    · iintro ⟨%PM, %VM, %FM, HP, HV, HF, %Hn⟩
      icases ((ownMap_fractional (GF := GF) pm PM).fractional q1 q2).1 $$ HP with ⟨HP1, HP2⟩
      icases ((ownMap_fractional (GF := GF) vm VM).fractional q1 q2).1 $$ HV with ⟨HV1, HV2⟩
      icases ((ownMap_fractional (GF := GF) fm FM).fractional q1 q2).1 $$ HF with ⟨HF1, HF2⟩
      isplitl [HP1 HV1 HF1]
      · iexists PM, VM, FM; iframe; ipureintro; exact Hn
      · iexists PM, VM, FM; iframe; ipureintro; exact Hn
    · iintro ⟨⟨%PM, %VM, %FM, HP, HV, HF, %Hn⟩, ⟨%PM', %VM', %FM', HP', HV', HF', -⟩⟩
      ihave %Ha := ownMap_agree pm _ _ PM PM' $$ [$HP $HP']
      ihave %Hb := ownMap_agree vm _ _ VM VM' $$ [$HV $HV']
      ihave %Hc := ownMap_agree fm _ _ FM FM' $$ [$HF $HF']
      subst Ha Hb Hc
      iexists PM, VM, FM
      isplitl [HP HP']
      · iapply ((ownMap_fractional (GF := GF) pm PM).fractional q1 q2).2; iframe
      isplitl [HV HV']
      · iapply ((ownMap_fractional (GF := GF) vm VM).fractional q1 q2).2; iframe
      isplitl [HF HF']
      · iapply ((ownMap_fractional (GF := GF) fm FM).fractional q1 q2).2; iframe
      ipureintro; exact Hn

section api
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## One run's names and v3rpc's shared invariant (the draft's §3) -/

/-- **One run's values**: the watch server's (`srv`) and the server's side of the watch path
(`W`), the gRPC stream's names (`γs`), the mvcc watch stream (`ws`, the interface value
`NewWatchStream` returned, and its API name `ι`), the registry `γreg` (id ↦ `RegInfo`, discarded
entries), the id tokens `γtok` (one per registered id), the received list `γr` (a mono list of `WResp`, the send loop's authority), the
close token `γcl`, the answer tokens' map (`γa`), the control stream (`ctrl`, its SPSC names), the
three maps, `closec` and its names. (The draft's `WRunA`, with the fields it keeps "unchanged" of
today's `WRun`; the gRPC stream `st`, the contents `Up`/`Dn` and the context `ci`/`cd` are
`swsIs`'s parameters, as the draft has them.) -/
structure WRun (GF : BundledGFunctors) where
  srv : WSrv GF
  W : SrvW GF
  γs : StreamNames
  /-- the mvcc watch stream, as the interface value `NewWatchStream` returned (the draft's `wsp :
  Loc`, read as `wspIface wsp`, would fix its dynamic type to `*watchStream`, which the API's
  `NewWatchStream` contract does not give: `notes/mvcc-migration/v3rpc.md`, finding F1) -/
  ws : GoInterface
  ι : mvcc.api.WsName
  γreg : GName
  γtok : GName
  γr : GName
  γcl : GName
  γa : GName
  ctrl : Loc
  γctrl : SpscNames
  pm : Loc
  vm : Loc
  fm : Loc
  cc : Loc
  γcc : ChanNames

/-- The run's ghost names its stream's auxiliary name publishes (`ι` is not a `GName`, and no
client needs it). -/
def auxOf (r : WRun GF) : List GName := [r.γreg, r.γtok, r.γr, r.γa]

theorem auxOf_inj {r r' : WRun GF} (h : auxOf r = auxOf r') :
    r.γreg = r'.γreg ∧ r.γtok = r'.γtok ∧ r.γr = r'.γr ∧ r.γa = r'.γa := by
  unfold auxOf at h
  simp only [List.cons.injEq, and_true] at h
  exact h

/-- **v3rpc's invariant of a run** (shared by `recvLoop`, `sendLoop`, `close`; the draft's
`wsInv`, `WatchApi.lean`'s `wsInvG` at the run's names): the stream's state `S`; the registry agrees
with `S` (every watcher's `RegInfo`, its discarded entries kept, so the snapshot can copy them; the
id tokens minted for exactly `S`'s ids); every watcher unfiltered; every watcher not live was
cancelled at the client's request (`cancelQ`: the reason today's `Ψ`/`rsnFor` carried); the stream
open, or the close token deposited. -/
abbrev wsInv (r : WRun GF) : IProp GF := wsInvG r.ι r.γreg r.γtok r.γcl (cancelQ r.γs)

/-! ## The per-message stream spec (the draft's §4) -/

/-- **The send loop's snapshot of the received responses `rs`** (the draft's `rcvSnap`,
`WatchApi.lean`'s `rcvSnapG` at the run's names; made right after the receive of `rs`'s last,
`snap_after_recv`): the API's watch guarantee at some state `σ` and stream state `S` of that
moment, the notified log's certified lower bound and the compaction revision's permit at it, each
of `S`'s watchers registered (`regIs`) and live or cancelled at the client's request. -/
abbrev rcvSnap (r : WRun GF) (rs : List mvcc.api.WResp) (σ : mvcc.api.MvccState)
    (S : mvcc.api.StreamState) : IProp GF :=
  rcvSnapG r.W r.γreg (cancelQ r.γs) rs σ S

/-- **A response of the mvcc watch stream sent at position `j`**: the response of the `n`-th
received response `x` (after `pre`), its header's revision `x`'s, its id (unless `-1`) live after
the `j` responses `L` sent before it; the received list's lower bound and the snapshot at
`pre ++ [x]`; for a `-1` response, every id live after `L` is a watcher of the snapshot's `S` (its
created response was sent before the receive, so it registered before the snapshot); if `x` has
events, its id's responses with events sent before `j`, then `x`, are its id's responses with
events received; no response before it came from `n`; what was forwarded before it (`fwdEvs`,
`fwdIdx`). -/
def mvccOk (r : WRun GF) (j : Nat) (m : WatchRespM) : IProp GF :=
  iprop(∃ (n : Nat) (x : mvcc.api.WResp) (pre : List mvcc.api.WResp) (L : List WatchRespM)
      (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState),
    ⌜m = mvccResp n x m.hdr ∧ m.hdr.revision = x.rev ∧ L.length = j ∧ pre.length = n ∧
      (x.id ≠ W64 (-1) → idLive L x.id) ∧
      (x.id = W64 (-1) → ∀ X, idLive L X → X ≠ W64 (-1) → (S.ws !! X).isSome) ∧
      (x.evs ≠ [] → sentEvsOf L x.id ++ [x] =
        ((pre ++ [x]).filter (fun y => decide (y.id = x.id))).filter (fun y => decide (y.evs ≠ []))) ∧
      (∀ m' ∈ L, ∀ y, m'.src ≠ some (n, y)) ∧ fwdIdx L n x ∧
      (∀ X, fwdEvs L pre x X)⌝ ∗
    monoListLbOwn r.γs.down L ∗ rcvLb r.γr (pre ++ [x]) ∗
    rcvSnap r (pre ++ [x]) σ S)

/-- **The watcher a created response names**: for a create request `c` answered by a registered
response `m`, its registry entry (the range of the request and the response's id; its first
revision the start revision, or for `0` the length of a certified notified log, `σ.log` at the
registration with nothing pending), its id token, the request's authorization (unchanged, at the
server's auth tag), and the stream's sent count at the registration (`wsSentLb ι k`, what the send
loop's drain matches; the client needs only `RegInfo.k`). -/
def ctrlWatcher (r : WRun GF) (tok : Option GoString) (req : WatchReqM) (m : WatchRespM) :
    IProp GF :=
  match req with
  | .create c => if m.canceled then iprop(True) else
      iprop(∃ i : RegInfo, ⌜createRangeOk c m.watchId i.rg⌝ ∗ regIs r.γreg m.watchId i ∗
        idTok r.γtok m.watchId ∗ mvcc.api.wsSentLb r.ι i.k ∗
        (if c.startRev = W64 0 then ∃ Lr : mvcc.Log, r.W.histLb Lr ∗ ⌜i.lo = Lr.length⌝
         else iprop(⌜i.lo = sint.nat c.startRev⌝)) ∗
        watchAuthed r.srv.tag r.srv.s tok c.bound c.key c.rangeEnd)
  | _ => iprop(True)

/-- **A created response sent at `j` follows the `-1` responses received before the watcher's
stamp** (from the drain, with `wsChan_recv`'s non-blocking receive): the send loop had received
`l` (at least the stamp `k` responses) and sent every `-1` among them before `j`. -/
def createdAfter (r : WRun GF) (j : Nat) (m : WatchRespM) : IProp GF :=
  if m.created && !m.canceled then
    iprop(∃ (i : RegInfo) (l : List mvcc.api.WResp) (L : List WatchRespM),
      regIs r.γreg m.watchId i ∗ rcvLb r.γr l ∗ monoListLbOwn r.γs.down L ∗
      ⌜i.k ≤ l.length ∧ L.length = j ∧
        ∀ (n : Nat) (x : mvcc.api.WResp), l[n]? = some x → x.id = W64 (-1) →
          ∃ m' ∈ L, m'.src = some (n, x)⌝)
  else iprop(True)

instance createdAfter_persistent (r : WRun GF) (j : Nat) (m : WatchRespM) :
    Persistent (createdAfter (GF := GF) r j m) := by
  unfold createdAfter; split <;> infer_instance

/-- **A control response**: it answers the request `req` the client sent at some position `i`
(`upAtW`), as `ctrlAnswers` says, with the request's answer token (`ansTok`: no request is
answered twice); a created response names its watcher's registry entry (`ctrlWatcher`). -/
def ctrlOk (r : WRun GF) (tok : Option GoString) (m : WatchRespM) : IProp GF :=
  iprop(∃ (i : Nat) (req : WatchReqM), upAtW r.γs i req ∗ ⌜ctrlAnswers req m⌝ ∗
    ctrlWatcher r tok req m ∗ ansTok r.γa i)

/-- **What the watch server says of its `j`th response**: the run's names published
(`streamAuxIs`), the header's ids, and a control response or an mvcc one. The run is existential:
the client agrees on it through `streamAuxIs`. -/
def watchDn (γs : StreamNames) (R : WSrv GF) (W : SrvW GF) (tok : Option GoString)
    (j : Nat) (m : WatchRespM) : IProp GF :=
  iprop(∃ r : WRun GF, ⌜r.srv = R ∧ r.W = W ∧ r.γs = γs⌝ ∗ streamAuxIs γs (auxOf r) ∗
    ⌜m.hdr.clusterId = R.cid ∧ m.hdr.memberId = R.mid⌝ ∗
    ((⌜m.src = none⌝ ∗ ctrlOk r tok m ∗ createdAfter r j m) ∨ mvccOk r j m))

/-- **The watch stream's specification** (the note's §4; persistent): the handler's content of
every response sent down is exactly `watchDn`. -/
def watchStreamSpec (γs : StreamNames) (R : WSrv GF) (W : SrvW GF) (tok : Option GoString)
    (Dn : Nat → WatchRespM → IProp GF) : IProp GF :=
  iprop(□ ∀ (j : Nat) (m : WatchRespM), Dn j m ∗-∗ watchDn γs R W tok j m)

instance watchStreamSpec_persistent (γs : StreamNames) (R : WSrv GF) (W : SrvW GF)
    (tok : Option GoString) (Dn : Nat → WatchRespM → IProp GF) :
    Persistent (watchStreamSpec γs R W tok Dn) := by
  unfold watchStreamSpec; infer_instance

/-! ## One run's `serverWatchStream` (the draft's §6) -/

/-- **A control response** `l` on the control stream: a response holding a model `m` with the
server's header ids, no ghost source, answering a request of the stream (`ctrlOk`, at the run's
context's token; with the request's answer token: not persistent). -/
def ctrlP (r : WRun GF) (ci : GoInterfaceOk) (_k : Int) (l : Loc) : IProp GF :=
  iprop(∃ m : WatchRespM, watchRespMsg l m ∗
    ⌜m.hdr.clusterId = r.srv.cid ∧ m.hdr.memberId = r.srv.mid ∧ m.src = none⌝ ∗
      ctrlOk r (auth.ctxTokenOf (GoInterface.ok ci)) m)

/-- **The run's `serverWatchStream` `sws`** (persistent; the draft's `swsIs2`): the fields, the
gRPC stream and its spec at the model, the client's content (`upOk`), the mvcc stream
(`isMvccWatchStream`, its interface value the field's), the run's invariant (`wsInv`), the server's
side (`srvWOk`), the control stream, `closec`, `mu`. -/
def swsIs (sws : Loc) (r : WRun GF) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(⌜sws ≠ null⌝ ∗ zapLoggerOk r.srv.lg ∗
    swsF sws go!"lg" ↦□ r.srv.lg ∗
    swsF sws go!"clusterID" ↦□ r.srv.cid ∗
    swsF sws go!"memberID" ↦□ r.srv.mid ∗
    swsF sws go!"maxRequestBytes" ↦□ r.srv.mrb ∗
    swsF sws go!"sg" ↦□ srvIface r.srv.s ∗
    swsF sws go!"watchable" ↦□ wsIface r.srv.wsl ∗
    swsF sws go!"ag" ↦□ srvIface r.srv.s ∗
    swsF sws go!"gRPCStream" ↦□ st ∗
    swsF sws go!"watchStream" ↦□ r.ws ∗
    swsF sws go!"ctrlStream" ↦□ r.ctrl ∗
    swsF sws go!"progress" ↦□ r.pm ∗
    swsF sws go!"prevKV" ↦□ r.vm ∗
    swsF sws go!"fragment" ↦□ r.fm ∗
    swsF sws go!"closec" ↦□ r.cc ∗
    watchSrvOk r.srv.s r.srv.E r.srv.tag ∗
    srvStreamIs st r.γs pbWatchRequest pbWatchResponse Up Dn ci cd ∗
    watchStreamSpec r.γs r.srv r.W (auth.ctxTokenOf (GoInterface.ok ci)) Dn ∗
    streamAuxIs r.γs (auxOf r) ∗
    upOk r.srv.E.authMode Up ∗
    mvcc.api.isMvccWatchStream r.ws r.W.γm r.ι ∗
    inv wsN (wsInv r) ∗
    srvWOk r.W r.srv.wsl wsN ∗
    isSpsc r.γctrl r.ctrl (ctrlP r ci) (fun _ => iprop(True)) ∗
    ownBroadcastChan r.cc r.γcc iprop(True) .Unknown ∗
    sync.isRWMutexGuard (hlc := HasLC.hasLC) (swsF sws go!"mu") (swsMu r.pm r.vm r.fm))

/-- `swsIs` is persistent (its mvcc parts by the API's `persistent.law`). -/
theorem swsIs_persistent (hP : mvcc.api.persistent.law (GF := GF)) (sws : Loc) (r : WRun GF)
    (Up : Nat → WatchReqM → IProp GF) (Dn : Nat → WatchRespM → IProp GF) (st : GoInterface)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (swsIs sws r Up Dn st ci cd) := by
  have : ∀ ws γ ι, Persistent (mvcc.api.isMvccWatchStream (GF := GF) ws γ ι) := hP.2.1
  have := srvWOk_persistent hP r.W r.srv.wsl wsN
  unfold swsIs; infer_instance

/-- **A run's resources** (what grpc's run slot holds for a watch stream; the draft's
`R.E.RD ∗ ⌜threadBound …⌝`): the auth store's reader resource (`isWatchPermitted`) and the thread
bound under which `GetProgressReportInterval` borrows a reader slot of the progress interval's lock
from the package's pool, and (the store's readers as client-held tokens, 2026-11-07) two reader
tokens of the store at the watch path's names (`mvccReaders W.γm 2`, one per loop: `lean`'s
`recvRes`/`sendRes` store reader slots; the API's `Watch`, `Rev`, `RequestProgress(All)` take one,
since 2026-11-07 without a thread token: the reader tokens carry the store's lock slots). No
thread token: `watchServer.Watch` needs none (the API's `Close` takes none). -/
def watchRunSlot (R : WSrv GF) (W : SrvW GF) : IProp GF :=
  iprop(R.E.RD ∗ mvcc.api.mvccReaders W.γm 2 ∗
    ⌜threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders⌝)

/-- **The watch method's stream specification** (unit W-W: `Spec` of the registered method):
`watchStreamSpec` at the server and its side of the watch path `W`, and (G2, 2026-10-30) the
stream's token `tok` its watchers' authorizations name (`watchAuthed`); the registration is at
`tok := auth.mdTokenOf md` for the stream's metadata `md`. -/
abbrev watchSpec (R : WSrv GF) (W : SrvW GF) (tok : Option GoString) :
    StreamSpec (GF := GF) pbWatchResponse :=
  fun γs Dn => watchStreamSpec γs R W tok Dn

/-- The watch method's stream specification is satisfiable per stream (`streamSpecOk`): its
content is `watchDn`. -/
theorem streamSpecOk_watchSpec (R : WSrv GF) (W : SrvW GF) (tok : Option GoString) :
    ⊢ streamSpecOk (watchSpec R W tok) := by
  unfold streamSpecOk
  iintro !> %γs
  iexists (watchDn γs R W tok)
  simp only [watchSpec]; unfold watchStreamSpec
  iintro !> !> %j %m
  isplit
  · iintro H; iexact H
  · iintro H; iexact H

end api

end defs

end v3rpc
end EtcdGrove
end Perennial
