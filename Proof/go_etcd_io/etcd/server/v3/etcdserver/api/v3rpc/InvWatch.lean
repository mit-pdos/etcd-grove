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
trust-boundary spec, `0 ≤ n`; `io.EOF` (`eofVar`) stays a premise: Perennial's `io` fact does not
keep it.)

**The server's contract** (`watchSrvOk s E γ wsl`, persistent): the server's KV is the watchable
store `wsl` (`mvcc.isWatchableStore wsl E.s γ`, its names over the apply thread's store names
`E.γ`), `Term()`/`Leader()` return (`raftStatusOk`), and its auth store (`isReqAuth`, A2's, and the
apply package's `isAuthStore`, both at the reader resource `E.RD`, the latter in the store's mode
`E.authOn`).

**The watch server** (`isWatchServer p R`, persistent): `NewWatchServer`'s `*watchServer`, its
fields fixed (`WSrv`: the server, its environment, the watchable store and its names, the cluster
and member ids, the logger, the request budget).

**One run** (`WRun`, `swsIs sws r`, persistent): the run's `serverWatchStream` `sws`, its fields
(the gRPC stream, the mvcc watch stream `wsp` with its channel, the control stream `ctrl` (an SPSC
channel from the receive loop to the send loop, `ctrlP`: each control response answers a request),
the three maps, `closec` (a broadcast channel)), and the lock `mu` (a `sync.RWMutex` guarding the
maps, `swsMu`: `prevKV` and `fragment` empty, the restrictions' consequence); unit W-M2: the
mvcc stream's id map and progress fact are its channel's, the progress fact the stream's
progress request (`progQ`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Proof.sync
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI

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
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The server `s` as an interface value (`apply.RaftStatusGetter`, `AuthGetter`). -/
abbrev srvIface (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s

/-- The watchable store `wsl` as `mvcc.WatchableKV`. -/
abbrev wsIface (wsl : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl

/-- The mvcc watch stream `wsp` as `mvcc.WatchStream`. -/
abbrev wspIface (wsp : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchStream.ty) #wsp

/-- The field `f` of the run's `serverWatchStream`. -/
abbrev swsF (sws : Loc) (f : GoString) : Loc := structFieldRef serverWatchStream f sws

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  icases Hi with ⟨-, -, -, -, -, -, -, #Hw⟩
  iunfold watchVars
  iframe Heof Hw

/-! ## The server's contract -/

/-- **The server's contract for the watch path** (persistent; see the file header). -/
def watchSrvOk (s : Loc) (E : apply.AEnv GF) (γ : mvcc.WsNames) (wsl : Loc) : IProp GF :=
  iprop(mvcc.isWatchableStore wsl E.s γ ∗ ⌜γ.st = E.γ⌝ ∗ raftStatusOk s ∗
    (∃ (st : GoInterface) (cca : Bool) (P : IProp GF) (f : val),
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st E.RD ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ apply.isAuthStore st E.γ P f E.RD E.authOn) ∗
    watchVars ∗ mvcc.watchTokPool γ)

instance watchSrvOk_persistent (s : Loc) (E : apply.AEnv GF) (γ : mvcc.WsNames) (wsl : Loc) :
    Persistent (watchSrvOk s E γ wsl) := by
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
watchable store and its names, the cluster and member ids, the logger, the request budget. -/
structure WSrv (GF : BundledGFunctors) where
  s : Loc
  E : apply.AEnv GF
  wsl : Loc
  γ : mvcc.WsNames
  cid : w64
  mid : w64
  lg : Loc
  mrb : w64

/-- **The `*watchServer` `p`** (persistent): its fields, the server's contract. -/
def isWatchServer (p : Loc) (R : WSrv GF) : IProp GF :=
  iprop(⌜p ≠ null ∧ R.lg ≠ null⌝ ∗
    structFieldRef watchServer go!"lg" p ↦□ R.lg ∗
    structFieldRef watchServer go!"clusterID" p ↦□ R.cid ∗
    structFieldRef watchServer go!"memberID" p ↦□ R.mid ∗
    structFieldRef watchServer go!"maxRequestBytes" p ↦□ R.mrb ∗
    structFieldRef watchServer go!"sg" p ↦□ srvIface R.s ∗
    structFieldRef watchServer go!"watchable" p ↦□ wsIface R.wsl ∗
    structFieldRef watchServer go!"ag" p ↦□ srvIface R.s ∗
    watchSrvOk R.s R.E R.γ R.wsl)

instance isWatchServer_persistent (p : Loc) (R : WSrv GF) : Persistent (isWatchServer p R) := by
  unfold isWatchServer; infer_instance

/-! ## The client's restrictions and budget -/

/-- **What the client's content of a request gives the server** (persistent): the request is
restricted (`watchReqOk`) and, for a create request, comes with a watch token of the store
(`mvcc.watchTok γ`: the watchable store's watcher budget, which mvcc's `Watch` spends). -/
def upOk (γ : mvcc.WsNames) (Up : Nat → WatchReqM → IProp GF) : IProp GF :=
  iprop(□ ∀ (i : Nat) (m : WatchReqM), Up i m -∗ ⌜watchReqOk m⌝ ∗
    (match m with
     | .create c => mvcc.watchTok γ ∗ mvcc.startRead γ c.sr c.startRev
     | _ => iprop(True)))

instance upOk_persistent (γ : mvcc.WsNames) (Up : Nat → WatchReqM → IProp GF) :
    Persistent (upOk γ Up) := by
  unfold upOk; infer_instance

/-- **The client's content of the watch method's requests** (unit W-W: what the client's `Send`
gives with each request, `Up` of the registered method): the request is restricted
(`watchReqOk`) and a create request comes with a watch token of the store. -/
def watchUp (γ : mvcc.WsNames) (_i : Nat) (m : WatchReqM) : IProp GF :=
  iprop(⌜watchReqOk m⌝ ∗
    (match m with
     | .create c => mvcc.watchTok γ ∗ mvcc.startRead γ c.sr c.startRev
     | _ => iprop(True)))

/-- The registered content meets the watch server's restrictions and budget (`upOk`). -/
theorem upOk_watchUp (γ : mvcc.WsNames) : ⊢ upOk (GF := GF) γ (watchUp γ) := by
  unfold upOk
  iintro !> %i %m H
  unfold watchUp
  iexact H

/-! ## One run -/

/-- **One run's values**: the watch server's, the gRPC stream (`st`, its names, the contents, the
run's context), the mvcc watch stream (`wsp`, its ghost names, its channel and names), the
answer tokens' map (`γa`, published with `γo` in the stream's auxiliary name), the
control stream (`ctrl`, its SPSC names), the three maps, `closec` and its names. -/
structure WRun (GF : BundledGFunctors) where
  srv : WSrv GF
  st : GoInterface
  γs : StreamNames
  Up : Nat → WatchReqM → IProp GF
  Dn : Nat → WatchRespM → IProp GF
  ci : GoInterfaceOk
  cd : context.ContextDesc (IProp GF)
  wsp : Loc
  γo : mvcc.WsStreamNames
  /-- the answer tokens' ghost map (the watch slice's unit W-C: `ansTok`, `ansPool`) -/
  γa : GName
  ch : Loc
  γc : mvcc.WatchChanNames
  ctrl : Loc
  γctrl : SpscNames
  pm : Loc
  vm : Loc
  fm : Loc
  cc : Loc
  γcc : ChanNames

/-- The watch params of the server's store. -/
abbrev wParams (R : WSrv GF) : mvcc.WatchParams GF := mvcc.storeWatchParams R.wsl R.E.s R.γ

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

/-- **A control response** `l` on the control stream: a response holding a model `m` with the
server's header ids, no ghost source, answering a request of the stream (`ctrlOk`, with the
request's answer token: not persistent). -/
def ctrlP (r : WRun GF) (_k : Int) (l : Loc) : IProp GF :=
  iprop(∃ m : WatchRespM, watchRespMsg l m ∗
    ⌜m.hdr.clusterId = r.srv.cid ∧ m.hdr.memberId = r.srv.mid ∧ m.src = none⌝ ∗
      ctrlOk r.γs r.srv.γ m)

/-- **The run's `serverWatchStream` `sws`** (persistent; see the file header). -/
def swsIs (sws : Loc) (r : WRun GF) : IProp GF :=
  iprop(⌜sws ≠ null ∧ r.srv.lg ≠ null⌝ ∗
    swsF sws go!"lg" ↦□ r.srv.lg ∗
    swsF sws go!"clusterID" ↦□ r.srv.cid ∗
    swsF sws go!"memberID" ↦□ r.srv.mid ∗
    swsF sws go!"maxRequestBytes" ↦□ r.srv.mrb ∗
    swsF sws go!"sg" ↦□ srvIface r.srv.s ∗
    swsF sws go!"watchable" ↦□ wsIface r.srv.wsl ∗
    swsF sws go!"ag" ↦□ srvIface r.srv.s ∗
    swsF sws go!"gRPCStream" ↦□ r.st ∗
    swsF sws go!"watchStream" ↦□ wspIface r.wsp ∗
    swsF sws go!"ctrlStream" ↦□ r.ctrl ∗
    swsF sws go!"progress" ↦□ r.pm ∗
    swsF sws go!"prevKV" ↦□ r.vm ∗
    swsF sws go!"fragment" ↦□ r.fm ∗
    swsF sws go!"closec" ↦□ r.cc ∗
    watchSrvOk r.srv.s r.srv.E r.srv.γ r.srv.wsl ∗
    srvStreamIs r.st r.γs pbWatchRequest pbWatchResponse r.Up r.Dn r.ci r.cd ∗
    watchStreamSpec r.γs r.srv.γ r.srv.cid r.srv.mid r.Dn ∗
    streamAuxIs r.γs (auxOf r.γo r.γa) ∗
    upOk r.srv.γ r.Up ∗
    mvcc.isWatchStream r.wsp (wsIface r.srv.wsl) (wParams r.srv) r.γo ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchStream go!"ch" r.wsp ↦□ r.ch ∗
    isChan r.ch r.γc.ch go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse ∗
    inv mvcc.watchN (mvcc.watchChanInv r.srv.γ r.ch r.γc) ∗
    isSpsc r.γctrl r.ctrl (ctrlP r) (fun _ => iprop(True)) ∗
    ownBroadcastChan r.cc r.γcc iprop(True) .Unknown ∗
    sync.isRWMutexGuard (hlc := HasLC.hasLC) (swsF sws go!"mu") (swsMu r.pm r.vm r.fm) ∗
    ⌜r.γo.ids = r.γc.ids ∧ r.γo.prog = r.γc.prog ∧ r.γo.sentl = r.γc.sentl ∧
      0 < sint.Z r.γc.ch.chanCap⌝ ∗
    savedPropOwn r.γo.prog DFrac.discard (progQ r.γs) ∗
    savedPredOwn r.γo.rsn DFrac.discard (cancelQ r.γs) ∗
    ⌜r.γo.regi = r.γc.regi ∧ r.γo.rsn = r.γc.rsn⌝)

instance swsIs_persistent (sws : Loc) (r : WRun GF) : Persistent (swsIs sws r) := by
  unfold swsIs; infer_instance

/-- **The receive loop's resources**: a reader slot of the watchable store (`Watch`, `Rev`,
`RequestProgressAll`) and the auth store's reader resource (`isWatchPermitted`). -/
def recvRes (R : WSrv GF) : IProp GF :=
  iprop(mvcc.watchReader R.wsl R.E.s R.γ ∗ R.E.RD)

/-- **The send loop's resources**: a reader slot of the watchable store (`RequestProgress`) and
a reader token of the progress interval's lock (`GetProgressReportInterval`). -/
def sendRes (R : WSrv GF) : IProp GF :=
  iprop(mvcc.watchReader R.wsl R.E.s R.γ ∗ sync.ownRWMutex (hlc := HasLC.hasLC) intervalMu intervalP)

/-- **A run's resources** (what grpc's run slot holds for a watch stream): the receive loop's
and the send loop's. -/
def watchRunSlot (R : WSrv GF) : IProp GF := iprop(recvRes R ∗ sendRes R)

/-- **The watch method's stream specification** (unit W-W: `Spec` of the registered method):
`watchStreamSpec` at the server's store names and ids. -/
abbrev watchSpec (R : WSrv GF) : StreamSpec (GF := GF) pbWatchResponse :=
  fun γs Dn => watchStreamSpec γs R.γ R.cid R.mid Dn

/-- The watch method's stream specification is satisfiable per stream (`streamSpecOk`): its
content is `watchDn`. -/
theorem streamSpecOk_watchSpec (R : WSrv GF) : ⊢ streamSpecOk (watchSpec R) := by
  unfold streamSpecOk
  iintro !> %γs
  iexists (watchDn γs R.γ R.cid R.mid)
  simp only [watchSpec]; unfold watchStreamSpec
  iintro !> !> %j %m
  isplit
  · iintro H; iexact H
  · iintro H; iexact H

end defs

end v3rpc
end EtcdGrove
end Perennial
