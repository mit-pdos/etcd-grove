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
maps, `swsMu`: `prevKV` and `fragment` empty, the restrictions' consequence).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Proof.sync

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

/-- The progress interval's lock (the package variable `progressReportIntervalMu`). -/
abbrev intervalMu : Loc := globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.progressReportIntervalMu

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

/-! ## Map and points-to lemmas (as `lease/LessorLemmas.lean`'s, without its package's
assumptions) -/

/-- Two shares of a map points-to agree on the map. -/
theorem ownMap_agree' {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    [go.IntoValInj V] (mref : Loc) (dq1 dq2 : DFrac) (m1 m2 : GMap K V) :
    ownMap (GF := GF) mref dq1 m1 ∗ ownMap (GF := GF) mref dq2 m2 ⊢ ⌜m1 = m2⌝ := by
  rw [ownMap_unseal]
  iintro ⟨H1, H2⟩
  unfold ownMapDef
  iNamedSuffix H1 "1"
  iNamedSuffix H2 "2"
  icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
  subst Hmv
  ipureintro
  apply GMap.ext
  intro k
  have h1 := Hagree1 k
  have h2 := Hagree2 k
  rw [← go.mapLookup_pure _ _ _ His_map1, go.mapLookup_pure _ _ _ His_map2] at h1
  rw [h1] at h2
  change m1 !! k = m2 !! k
  cases hk1 : m1 !! k <;> cases hk2 : m2 !! k <;> simp only [hk1, hk2] at h2
  · rfl
  · cases h2
  · cases h2
  · simp only [Prod.mk.injEq, true_and] at h2
    rw [go.intoVal_inj h2]

/-- A map points-to splits and combines by fraction. -/
theorem ownMap_fractional' {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V]
    [go.IntoValInj K] (mref : Loc) (m : GMap K V) :
    Fractional (fun q : Qp => (ownMap (GF := GF) mref (DFrac.own q) m : IProp GF)) where
  fractional p q := by
    rw [ownMap_unseal]
    have hh := fun mv => (heapPointsto_fractional mref mv).fractional p q
    constructor
    · iintro H
      unfold ownMapDef
      iNamed H
      icases (hh mv).1 $$ Hown with ⟨H1, H2⟩
      isplitl [H1]
      · iexists mv, mp; simp only [named]; iframe H1; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
      · iexists mv, mp; simp only [named]; iframe H2; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
    · iintro ⟨H1, H2⟩
      unfold ownMapDef
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
      subst Hmv
      iexists mv, mp
      simp only [named]
      isplitl [Hown1 Hown2]
      · iapply (hh mv).2; iframe
      ipureintro; exact ⟨His_map2, Hagree2, Hdom2, Hdefault2⟩

/-- A points-to at `q1 + q2` in two parts. -/
theorem ptsto_frac_add' {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (q1 q2 : Qp) :
    typedPointsto (GF := GF) l v (DFrac.own (q1 + q2)) ⊣⊢
      typedPointsto (GF := GF) l v (DFrac.own q1) ∗ typedPointsto (GF := GF) l v (DFrac.own q2) :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own q1) (DFrac.own q2)

/-! ## The package facts -/

/-- The package variable `g` holds a fixed error whose `Error()` returns (persistent). -/
def msgErrVar (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ errMsgOk e)

instance msgErrVar_persistent (g : GoString) : Persistent (msgErrVar (GF := GF) g) := by
  unfold msgErrVar errMsgOk; infer_instance

/-- The package variable `g` holds a fixed histogram whose `Observe` returns (persistent). -/
def histVar (g : GoString) : IProp GF :=
  iprop(∃ h : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok h ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x))
      {{ RET #(); True }}))

instance histVar_persistent (g : GoString) : Persistent (histVar (GF := GF) g) := by
  unfold histVar; infer_instance

/-- **The progress interval** at the fraction `q` (what `progressReportIntervalMu` guards): a
duration of at least `10` nanoseconds (`GetProgressReportInterval`'s jitter `rand.Int63n(d / 10)`
needs `d / 10 > 0`) and at most `2 ^ 62` (`d + d / 10` must not wrap:
`issues/etcd-watch-progress-interval-overflow.md`). -/
def intervalP (q : Qp) : IProp GF :=
  iprop(∃ d : w64, typedPointsto (globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.progressReportInterval)
      d (DFrac.own q) ∗ ⌜10 ≤ sint.Z d ∧ sint.Z d ≤ 2 ^ 62⌝)

instance intervalP_fractional : Fractional (intervalP (GF := GF)) where
  fractional q1 q2 := by
    unfold intervalP
    constructor
    · iintro ⟨%d, Hd, %Hb⟩
      icases (ptsto_frac_add' _ _ q1 q2).1 $$ Hd with ⟨H1, H2⟩
      isplitl [H1]
      · iexists d; iframe; ipureintro; exact Hb
      · iexists d; iframe; ipureintro; exact Hb
    · iintro ⟨⟨%d1, H1, %Hb⟩, ⟨%d2, H2, -⟩⟩
      icombine H1 H2 gives %Hd
      subst Hd
      iexists d1
      isplitl [H1 H2]
      · iapply (ptsto_frac_add' _ _ q1 q2).2; iframe
      · ipureintro; exact Hb

/-- **mvcc's `ReportEventReceived(n)`** (names only: a metric) returns. -/
def reportEventOk : IProp GF :=
  iprop(□ ∀ n : w64, {{ True }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) (Val #n))
    {{ RET #(); True }})

instance reportEventOk_persistent : Persistent (reportEventOk (GF := GF)) := by
  unfold reportEventOk; infer_instance

/-- **`io.EOF`** (persistent): a fixed `errors.New` error (a pointer leaf with an `Error()`, of a
type that implements `error`: `context.isTypedErr`). -/
def eofVar : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr _root_.Perennial.io.EOF ↦□ GoInterface.ok e ∗
    ⌜errLeaf e ∧ context.isTypedErr (GoInterface.ok e)⌝ ∗ errMsgOk e)

instance eofVar_persistent : Persistent (eofVar (GF := GF)) := by
  unfold eofVar errMsgOk; infer_instance

/-- **The package facts `watch.go` reads** (persistent; see the file header). -/
def watchVars : IProp GF :=
  iprop(eofVar ∗
    errVarLeaf (hlc := HasLC.hasLC) go_etcd_io.etcd.server.v3.auth.ErrInvalidAuthToken ∗
    errVarLeaf (hlc := HasLC.hasLC) go_etcd_io.etcd.server.v3.auth.ErrAuthOldRevision ∗
    errVarLeaf (hlc := HasLC.hasLC) go_etcd_io.etcd.server.v3.auth.ErrUserEmpty ∗
    errVarLeaf (hlc := HasLC.hasLC) go_etcd_io.etcd.server.v3.auth.ErrPermissionDenied ∗
    errVarLeaf (hlc := HasLC.hasLC) go_etcd_io.etcd.server.v3.storage.mvcc.ErrEmptyWatcherRange ∗
    errVarLeaf (hlc := HasLC.hasLC) go_etcd_io.etcd.server.v3.storage.mvcc.ErrWatcherDuplicateID ∗
    msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted ∗
    msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidAuthToken ∗
    msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCAuthOldRevision ∗
    msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUserEmpty ∗
    msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPermissionDenied ∗
    msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCWatchCanceled ∗
    (∃ cv : Loc, globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.streamFailures ↦□ cv) ∗
    histVar go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchSendLoopWatchStreamDuration ∗
    histVar go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchSendLoopWatchStreamDurationPerEvent ∗
    histVar go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchSendLoopControlStreamDuration ∗
    histVar go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchSendLoopProgressDuration ∗
    (∃ tr : GoInterfaceOk, globalAddr go_etcd_io.etcd.pkg.v3.traceutil.Tracer ↦□ GoInterface.ok tr) ∗
    go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ctxCanceledPtr ∗
    reportEventOk ∗
    sync.isRWMutexGuard (hlc := HasLC.hasLC) intervalMu intervalP)

instance watchVars_persistent : Persistent (watchVars (GF := GF)) := by
  unfold watchVars; infer_instance

/-! ## The server's contract -/

/-- **The server's contract for the watch path** (persistent; see the file header). -/
def watchSrvOk (s : Loc) (E : apply.AEnv GF) (γ : mvcc.WsNames) (wsl : Loc) : IProp GF :=
  iprop(mvcc.isWatchableStore wsl E.s γ ∗ ⌜γ.st = E.γ⌝ ∗ raftStatusOk s ∗
    (∃ (st : GoInterface) (cca : Bool) (P : IProp GF) (f : val),
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st E.RD ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ apply.isAuthStore st P f E.RD E.authOn) ∗
    watchVars)

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
     | .create _ => mvcc.watchTok γ
     | _ => iprop(True)))

instance upOk_persistent (γ : mvcc.WsNames) (Up : Nat → WatchReqM → IProp GF) :
    Persistent (upOk γ Up) := by
  unfold upOk; infer_instance

/-! ## One run -/

/-- **One run's values**: the watch server's, the gRPC stream (`st`, its names, the contents, the
run's context), the mvcc watch stream (`wsp`, its open token's name, its channel and names), the
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
  γo : GName
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
      icases ((ownMap_fractional' (GF := GF) pm PM).fractional q1 q2).1 $$ HP with ⟨HP1, HP2⟩
      icases ((ownMap_fractional' (GF := GF) vm VM).fractional q1 q2).1 $$ HV with ⟨HV1, HV2⟩
      icases ((ownMap_fractional' (GF := GF) fm FM).fractional q1 q2).1 $$ HF with ⟨HF1, HF2⟩
      isplitl [HP1 HV1 HF1]
      · iexists PM, VM, FM; iframe; ipureintro; exact Hn
      · iexists PM, VM, FM; iframe; ipureintro; exact Hn
    · iintro ⟨⟨%PM, %VM, %FM, HP, HV, HF, %Hn⟩, ⟨%PM', %VM', %FM', HP', HV', HF', -⟩⟩
      ihave %Ha := ownMap_agree' pm _ _ PM PM' $$ [$HP $HP']
      ihave %Hb := ownMap_agree' vm _ _ VM VM' $$ [$HV $HV']
      ihave %Hc := ownMap_agree' fm _ _ FM FM' $$ [$HF $HF']
      subst Ha Hb Hc
      iexists PM, VM, FM
      isplitl [HP HP']
      · iapply ((ownMap_fractional' (GF := GF) pm PM).fractional q1 q2).2; iframe
      isplitl [HV HV']
      · iapply ((ownMap_fractional' (GF := GF) vm VM).fractional q1 q2).2; iframe
      isplitl [HF HF']
      · iapply ((ownMap_fractional' (GF := GF) fm FM).fractional q1 q2).2; iframe
      ipureintro; exact Hn

/-- **A control response** `l` on the control stream (persistent): a response holding a model
`m` with the server's header ids, no ghost source, answering a request of the stream
(`ctrlOk`). -/
def ctrlP (r : WRun GF) (_k : Int) (l : Loc) : IProp GF :=
  iprop(∃ m : WatchRespM, watchRespMsg l m ∗
    ⌜m.hdr.clusterId = r.srv.cid ∧ m.hdr.memberId = r.srv.mid ∧ m.src = none⌝ ∗ ctrlOk r.γs m)

instance ctrlP_persistent (r : WRun GF) (k : Int) (l : Loc) : Persistent (ctrlP r k l) := by
  unfold ctrlP; infer_instance

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
    upOk r.srv.γ r.Up ∗
    mvcc.isWatchStream r.wsp (wsIface r.srv.wsl) (wParams r.srv) r.γo ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchStream go!"ch" r.wsp ↦□ r.ch ∗
    isChan r.ch r.γc.ch go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse ∗
    inv mvcc.watchN (mvcc.watchChanInv r.srv.γ r.ch r.γc) ∗
    isSpsc r.γctrl r.ctrl (ctrlP r) (fun _ => iprop(True)) ∗
    ownBroadcastChan r.cc r.γcc iprop(True) .Unknown ∗
    sync.isRWMutexGuard (hlc := HasLC.hasLC) (swsF sws go!"mu") (swsMu r.pm r.vm r.fm))

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

end defs

end v3rpc
end EtcdGrove
end Perennial
