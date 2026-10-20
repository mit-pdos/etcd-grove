/-
**The client's watch (`client/v3/watch.go`) over etcd's Watch stream: the shared definitions**
(the watch slice's unit W-C, 2026-10-15; `notes/STATUS.md`, "W-C"; `notes/decisions.md`, "The
client's watch over the stream"). Lean-first, no Rocq counterpart.

**The goal.** `isEtcdRangeWatcher (EM := v3rpc.etcdModelOfServer R.E) w pfx` for the `*watcher`
`w` that `NewWatchFromWatchClient(wc, c)` returns over a stub `wc` on a connection to etcd's
server (`ServerWatcher.lean`). This file holds what the specs of `watch.go`'s functions share.

**The watcher** (`isClientWatcher w V`, persistent): its read-only fields (the stub, the call options,
the logger), its lock `mu` guarding the streams map (`watcherMu`: `nil` after `Close`, otherwise
a map of `*watchGRPCStream`s, each `isWGS`), and the facts about the server (`watchSrvFacts`).

**A gRPC watch stream's goroutines** (`watchGRPCStream`, one per context key): `run` (the only
sender on the gRPC stream, the owner of the stream's mutable fields: `substreams`, `resuming`,
`closeErr`, `resumec`), `serveWatchClient` (the only receiver, forwarding each response, in
order, on `respc`: an SPSC channel whose `k`th element is the stream's `k`th response with its
content `Dn k m`, `respcElem`), and one `serveSubstream` per watch (`watcherStream`), fed by
`run` on its `recvc` (an SPSC channel, `recvElem`: each response with the contract's facts
already established by `run`, relative to a cursor `γhi`), publishing on its `outc` (the
contract's SPSC channel, `rangeWatchElem`). The channels between them: `reqc` (the `Watch`
requests, a bag, `reqP`), `closingc` (the substreams that stopped, a bag with their remaining
resources, `closingP`), `errc` (the receive's error, a bag, `errP`), `donec` (closed once `run`
stopped, publishing `closeErr`, `closeErrPub`), each watch's `retc` (its channel, with the
consumer's resources, `retcP`).

**The premises about the server and the transport** (persistent; `watchSrvFacts`):
* the stub, the connection and the registration of etcd's `Watch` stream (`isGrpcStream` with
  `watchUp`/`watchSpec`, what `etcd_watch_served*` give);
* the watch-token pool (`mvcc.watchTokPool`, 2026-10-18: a create, and so every `Watch`, spends
  a token, which `run` takes from the pool for a time receipt of its own Go step: D19b's
  method, in place of the unbounded supply `watchTokSupply`);
* (no longer a premise, D24, 2026-10-20) `noRetryableStreamErr`, that no stream error has the
  status code `Unavailable` or `Internal`, the codes `isHaltErr` lets `run` retry on: the
  reconnection (`newWatchClient` after `errc`, the resume queue, `waitCancelSubstreams`) is
  verified at every call.
* (no longer a premise, unit W-M3) S4: a watch event's revision is reached (`rangeWatchEvOk`'s
  `etcdReached e.rev`). A watcher's deliveries are the watch events of a *watched* log
  (`watchRecvOk` carries `mvcc.evLog`: sealed, so the clients' model's `etcdState`/`EtcdStep` of
  the events are theorems, unit W-M2b; and certified by the store's caller, `certOk`, which the
  apply thread mints for a committed entry's log before applying it), and `etcdReached` is over
  certified logs (`v3rpc.srvReachedAt`), so `ev_ok` proves it (`etcdReached_of_certOk`). A
  linearizable read's floor comes from the client's atomic update at the committed KV state
  (`kvAnyAu`), which extends every certified log, not from mvcc's committed log, so a revision
  notified before mvcc commits it is reached without making a serializable read's floor false
  (`notes/STATUS.md`, "W-M3").
* (no longer premises, unit W-M2) S2 `srvProgressAllAnswers` (a response of watch id `-1` answers
  a progress request) and S3 `srvEventIdsAssigned` (a response with events carries an id the
  stream assigned to its watcher) are theorems (`srvProgressAllAnswers_holds`,
  `srvEventIdsAssigned_holds`: projections of `v3rpc.mvccOk`'s `mvccExtra`, which the send loop
  establishes from mvcc's channel invariant);
* `srvNoDupKeys`: no revision of the server writes a key twice (etcd's check lets some
  transactions do it: `issues/etcd-txn-check-intervals-sibling.md`; the recipes' and the cache's
  never do);
* the watches' prefix is not empty (`V.pfx ≠ []`: the server reads an empty key as `"\x00"`, so a
  watch of the key `""` would be sent the events of `"\x00"`; a non-empty prefix rules it out);
* the server's store names agree with its environment's (`R.γ.st = R.E.γ`) and its sealed
  logs are small (`srvLogsSmall`, the read path's `storeSmall`);
* package facts: `io.EOF`, `errors.New`'s errors and every context's `Err()` are errors the
  client's `status` and `errors` calls accept (`eofOk`, `errorsNewOk`, `ctxErrClientAllW`), and
  `watch.go`'s package variables (`clientWatchVars`).

**Progress requests** (`RequestProgress`, unit K2e-9): a `*progressRequest` on `reqc` (`reqP`),
which `run` forwards; the server's `-1` answer is broadcast to every registered substream (its
panic on a canceled substream's closed `recvc`, `issues/etcd-watch-progress-closed-substream.md`,
is fixed in the verified fork).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClientModel
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvClient
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Spec.google_golang_org.grpc.status.FromError
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Proof.go_etcd_io.etcd.client.v3.SyncSpsc
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostMap
public import Perennial.Proof.sync
public import Proof.go_etcd_io.etcd.client.v3.InvWatchWg

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3
open go_etcd_io.etcd.cache.v3

/-! ## The environment -/

section envs
variable [ext : FfiSyntax]

/-- **What a watcher is over** (fixed by `NewWatchFromWatchClient`): the watch server's values
(`R`: its store's names, its ids, its environment), the address it is served at and the client's
connection to it (its stream interceptors `ics`), the stub (`wc`, a `*watchClient`), the prefix
the watches are under (`pfx`), the logger (`lg`). -/
structure WEnv (GF : BundledGFunctors) where
  R : v3rpc.WSrv GF
  addr : GoString
  ics : List GoFunc
  conn : Loc
  wc : Loc
  pfx : GoString
  lg : Loc

end envs

section addrs
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- The stub as a `pb.WatchClient` interface value. -/
abbrev wcIface (wc : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType etcdserverpb.watchClient.ty) #wc

/-- **The `clientv3.Watcher` interface value of the `*watcher` `w`**: its methods are
`watcher`'s. -/
abbrev watcherIfaceOf (w : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty) #w

/-- A field of a `*watcher`. -/
abbrev watcherF (w : Loc) (f : GoString) : Loc := structFieldRef go_etcd_io.etcd.client.v3.watcher f w

/-- A field of a `*watchGRPCStream`. -/
abbrev wgsF (wgs : Loc) (f : GoString) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.watchGRPCStream f wgs

/-- A field of a `*watcherStream`. -/
abbrev wsF (ws : Loc) (f : GoString) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.watcherStream f ws

/-- A field of a substream's `initReq` (a `watchRequest` held in the `*watcherStream`). -/
abbrev wsReqF (ws : Loc) (f : GoString) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.watchRequest f (wsF ws go!"initReq")

/-- A field of a `*watchRequest`. -/
abbrev wrF (wr : Loc) (f : GoString) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.watchRequest f wr

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The clients' model at the watcher's server. -/
abbrev WEnv.EM (V : WEnv GF) : EtcdModel GF := v3rpc.etcdModelOfServer V.R.E

/-! ## The premises about the server and the transport -/

/-- **(S2) A response of watch id `-1` answers a progress request** (persistent; a premise until
unit W-M2, now a theorem: `srvProgressAllAnswers_holds`). -/
def srvProgressAllAnswers (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(□ ∀ (γs : StreamNames) (j : Nat) (m : v3rpc.WatchRespM), v3rpc.mvccOk γs R.γ j m -∗
    ⌜m.watchId = W64 (-1)⌝ -∗ ∃ i : Nat, v3rpc.upAtW γs i .progress)

instance srvProgressAllAnswers_persistent (R : v3rpc.WSrv GF) :
    Persistent (srvProgressAllAnswers R) := by
  unfold srvProgressAllAnswers; infer_instance

/-- **(S3) A response with events carries an id the stream assigned to its watcher** (persistent;
every create being auto-id, `watchReqOk`; a premise until unit W-M2, now a theorem:
`srvEventIdsAssigned_holds`). -/
def srvEventIdsAssigned (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(□ ∀ (γs : StreamNames) (j : Nat) (m : v3rpc.WatchRespM) (r : mvcc.RespM),
    v3rpc.mvccOk γs R.γ j m -∗ ⌜m.src = some r ∧ r.evs ≠ []⌝ -∗
    ∃ (γo : mvcc.WsStreamNames) (γa : GName), streamAuxIs γs (v3rpc.auxOf γo γa) ∗
      mvcc.idAssigned γo r.id r.w)

instance srvEventIdsAssigned_persistent (R : v3rpc.WSrv GF) :
    Persistent (srvEventIdsAssigned R) := by
  unfold srvEventIdsAssigned; infer_instance

/-- **(S2) holds of the verified server** (unit W-M2): `mvccOk`'s `mvccExtra` (the channel's
progress fact, saved by the handler as its progress request, `v3rpc.progQ`). -/
theorem srvProgressAllAnswers_holds (R : v3rpc.WSrv GF) : ⊢ srvProgressAllAnswers R := by
  iunfold srvProgressAllAnswers
  iintro !> %γs %j %m #Hok %Hid
  iunfold v3rpc.mvccOk at Hok
  icases Hok with ⟨%r, %rs, %L, %Hm, -, -, -, #Hx, -, -⟩
  iunfold v3rpc.mvccExtra at Hx
  icases Hx with ⟨-, #Hp⟩
  have hr : r.id = W64 (-1) := by
    have := congrArg v3rpc.WatchRespM.watchId Hm.1
    simp only [v3rpc.mvccResp] at this
    rw [← this]; exact Hid
  ihave #Hq := Hp $$ %hr
  iunfold v3rpc.progQ at Hq
  iexact Hq

/-- **(S3) holds of the verified server** (unit W-M2): `mvccOk`'s `mvccExtra` (the registration
fact the channel's invariant keeps, recorded by the stream's callback at the registration). -/
theorem srvEventIdsAssigned_holds (R : v3rpc.WSrv GF) : ⊢ srvEventIdsAssigned R := by
  iunfold srvEventIdsAssigned
  iintro !> %γs %j %m %r0 #Hok %Hs
  iunfold v3rpc.mvccOk at Hok
  icases Hok with ⟨%r, %rs, %L, %Hm, -, -, -, #Hx, -, -⟩
  iunfold v3rpc.mvccExtra at Hx
  icases Hx with ⟨#He, -⟩
  have hr : r = r0 := by
    have := congrArg v3rpc.WatchRespM.src Hm.1
    simp only [v3rpc.mvccResp] at this
    rw [Hs.1] at this; exact (Option.some.inj this).symm
  subst hr
  iapply He
  ipureintro; exact Or.inl Hs.2

/-- **The server's sealed logs are small** (persistent; the read path's `storeSmall`, unit
W-M2b: over `mvcc.idxSealed`, the logs the watch events are of). -/
def srvLogsSmall (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(□ ∀ log : mvcc.Log, mvcc.idxSealed R.γ.st.idx log -∗ ⌜txn.LogSmall log⌝)

instance srvLogsSmall_persistent (R : v3rpc.WSrv GF) : Persistent (srvLogsSmall R) := by
  unfold srvLogsSmall; infer_instance

/-- **No revision of the server writes a key twice** (a premise, persistent): every sealed log
of the server (`mvcc.idxSealed`, unit W-M2b: the logs the watch events are of) that is
certified (`mvcc.certOk`, D23, 2026-10-20: as a watch event's log is, `mvcc.evLog`; with an
update at `⊤`, to open the server's invariants that say what the certified logs hold) has each
revision's keys distinct (`txn.NoDupKeysPerRev`). etcd's check of a transaction's requests lets a
nested transaction's put and a later sibling's delete of one key through
(`issues/etcd-txn-check-intervals-sibling.md`); such a revision's put event carries a key-value
not in the state at its revision, against `rangeWatchEvOk`. The justification is per revision,
of what the transaction writes: whether the revision is committed yet or only sealed does not
matter. The recipes' and the cache's transactions never write a key twice: the premise is about
other writers. -/
def srvNoDupKeys (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(□ ∀ log : mvcc.Log, mvcc.idxSealed R.γ.st.idx log -∗ mvcc.certOk R.γ.st log ={⊤}=∗
    ⌜txn.NoDupKeysPerRev log⌝)

instance srvNoDupKeys_persistent (R : v3rpc.WSrv GF) : Persistent (srvNoDupKeys R) := by
  unfold srvNoDupKeys; infer_instance

/-- **`errors.New`'s errors are client errors grpc's `status` accepts** (a package fact of
`errors`, persistent: an `*errorString` is a leaf error with `Error` only; Perennial's model of
`errors.New` says it is a pointer error whose `Error()` returns the message, and the model has no
method sets). -/
def errorsNewOk : IProp GF :=
  iprop(□ ∀ (msg : GoString) (Φ : val → IProp GF),
    ▷ (∀ e : GoInterface, ⌜e ≠ GoInterface.nil ∧ clientErr e⌝ -∗ statusErrOk e -∗ Φ #e) -∗
    WP (App (Val (@! _root_.Perennial.errors.New)) (Val #msg)) {{ Φ }})

instance errorsNewOk_persistent : Persistent (errorsNewOk (GF := GF)) := by
  unfold errorsNewOk; infer_instance

/-- **Every context's `Err()` returns client errors** (a premise, persistent; as V2b's
`ctxErrClientAll`, which this file cannot import). -/
def ctxErrClientAllW : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
    context.isContext ctx cs -∗ ctxErrClient ctx cs)

instance ctxErrClientAllW_persistent : Persistent (ctxErrClientAllW (GF := GF)) := by
  unfold ctxErrClientAllW; infer_instance

/-- **`watch.go`'s package variables** (persistent; assumptions about the package's
initialization, as `clientv3Init`): `valCtxCh`, `zeroTime`, `maxBackoff`, never written. -/
def clientWatchVars : IProp GF :=
  iprop(∃ (ch : GoChan) (t : _root_.Perennial.time.Time) (d : _root_.Perennial.time.Duration),
    globalAddr go_etcd_io.etcd.client.v3.valCtxCh ↦□ ch ∗
    globalAddr go_etcd_io.etcd.client.v3.zeroTime ↦□ t ∗
    globalAddr go_etcd_io.etcd.client.v3.maxBackoff ↦□ d)

instance clientWatchVars_persistent : Persistent (clientWatchVars (GF := GF)) := by
  unfold clientWatchVars; infer_instance

/-- **The facts about the server, the transport and the packages a watcher rests on, but the
stub** (persistent; see the file header). -/
def watchConnFacts (V : WEnv GF) : IProp GF :=
  iprop(grpcConn V.conn V.addr V.ics [] ∗
    isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) V.addr
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp V.R.γ) (v3rpc.watchSpec V.R) ∗
    v3rpc.watchDescOk ∗ mvcc.watchTokPool V.R.γ ∗
    srvLogsSmall V.R ∗ srvNoDupKeys V.R ∗
    eofOk ∗ errorsNewOk ∗ ctxErrClientAllW ∗ clientWatchVars ∗ ⌜V.R.γ.st = V.R.E.γ ∧ V.pfx ≠ []⌝)

instance watchConnFacts_persistent (V : WEnv GF) : Persistent (watchConnFacts V) := by
  unfold watchConnFacts; infer_instance

/-- **The facts a watcher rests on** (persistent): the stub and `watchConnFacts`. -/
def watchSrvFacts (V : WEnv GF) : IProp GF :=
  iprop(v3rpc.watchStubAt V.wc V.conn ∗ watchConnFacts V)

instance watchSrvFacts_persistent (V : WEnv GF) : Persistent (watchSrvFacts V) := by
  unfold watchSrvFacts; infer_instance

/-- The create request `toPB` builds from a watch request's fields: the key and range end, the
start revision, the progress flag, no filter, no previous key-values, the automatic id, no
fragments. -/
def createOf (key ed : GoString) (rv : w64) (pn : Bool) (sr : Bool) : v3rpc.CreateReqM :=
  { key := key, rangeEnd := ed, startRev := rv, progressNotify := pn, filters := [],
    prevKv := false, watchId := W64 0, fragment := false, sr := sr }

/-! ## One watch: its request and its substream -/

/-- **A watch's start** (persistent; K2e-6, K2e-7d): for a watch registered with `sr`, its start
revision was read from the server's store (`mvcc.startRead`) and etcd had reached the revision
before it. -/
def startOk (V : WEnv GF) (sr : Bool) (rev : w64) : IProp GF :=
  iprop(mvcc.startRead V.R.γ sr rev ∗ (⌜sr = false⌝ ∨ etcdReached (EM := V.EM) (rev - W64 1)))

instance startOk_persistent (V : WEnv GF) (sr : Bool) (rev : w64) :
    Persistent (startOk V sr rev) := by
  unfold startOk; infer_instance

theorem startOk_read (V : WEnv GF) (sr : Bool) (rev : w64) :
    startOk V sr rev ⊢ mvcc.startRead V.R.γ sr rev := by
  unfold startOk; iintro ⟨#H, -⟩; iexact H

/-- **A watch's values** (fixed when `run` takes its request): the request's model (`o`, the start
revision `rev`), its context (`ctx`, `cs`), its `watchRequest`'s fields (`key`, `ed` the range end,
`cn`/`pn` the created and progress notifications, `wbl` the buffer logging, `flt` the filters'
slice), its `retc` channel (a bag), and its substream `ws` (`*watcherStream`) with the substream's
channels (`outc` the caller's, an SPSC channel with names `γ`; `recvc` from `run`, a synchronous
SPSC with names `γr` and the dispatch cursor `γhi`; D24: the `donec` of each of its goroutines'
lifetimes is the lifetime's, `LifePrm`). -/
structure WsPrm (GF : BundledGFunctors) where
  o : OpFull
  rev : w64
  ctx : GoInterfaceOk
  cs : context.ContextDesc (IProp GF)
  key : GoString
  ed : GoString
  cn : Bool
  pn : Bool
  wbl : Bool
  flt : GoSlice
  retc : Loc
  γret : ChanNames
  ws : Loc
  γ : EtcdWatchNames
  outc : Loc
  recvc : Loc
  γr : SpscNames
  γhi : GName
  /-- (K2e-7) the dispatch's second cursor (the cache's contract's positions, `recvCmpl`) -/
  γh2 : GName
  /-- the substream's goroutine has stopped for good (a one-shot flag: `false`, owned by the
  goroutine while it runs; `true`, read-only, published by its `donec`) -/
  γx : GName
  /-- (K2e-6) the watch's start revision was read from the server's store (`mvcc.startRead`):
  its create request says so (`CreateReqM.sr`) -/
  sr : Bool
  /-- (D24) the status of `recvc`'s positions: a ghost map from a position to whether a goroutine
  of the substream started there (`true`, `lifeStart`) or `run` sent a response there that is not
  a created one (`false`, `notStart`): a goroutine's first response is its create's -/
  γps : GName

/-- **The watch promises completeness** (K2e-7d): its start revision was read from the server's
store (`sr`), a non-zero one, and it is a prefix watch of a non-empty key not all `0xff` (its range
end neither empty nor `[0]`, so that the registered range covers exactly the keys under it,
`covers_prefix`). -/
def cplCond (sr : Bool) (o : OpFull) (rev : w64) : Bool :=
  sr && decide (o.key ≠ [] ∧ o.base.rangeEnd = prefixRangeEnd o.key ∧
    prefixRangeEnd o.key ≠ [W8 0] ∧ rev ≠ W64 0)

/-- `cplCond` of a watch's values. -/
abbrev cplOf (P : WsPrm GF) : Bool := cplCond P.sr P.o P.rev

/-- **The request is one of the contract's** (pure): a range watch under `pfx` from `rev ≥ 0`
(`isRangeWatch`, `OpWatch` not panicking) whose `watchRequest` fields are the model's. -/
def wsReqOk (pfx : GoString) (P : WsPrm GF) : Prop :=
  P.o.isRangeWatch P.rev = true ∧ ¬ P.o.watchPanics ∧ 0 ≤ sint.Z P.rev ∧
    KeyRangeUnder pfx P.o.key P.o.base.rangeEnd ∧
    P.key = P.o.key ∧ P.ed = P.o.base.rangeEnd ∧ P.cn = P.o.base.createdNotify ∧
    P.pn = P.o.base.progressNotify

/-- **What a watch's `retc` carries** (the bag's value predicate): the substream's `outc`, the
contract's SPSC channel, with the consumer's resources (`Watch` returns them). -/
def retcP (V : WEnv GF) (o : OpFull) (rev : w64) (sr : Bool) (outc : Loc) : IProp GF :=
  iprop(∃ γ : EtcdWatchNames,
    isSpsc γ.spsc outc (rangeWatchElem (EM := V.EM) γ V.pfx o rev) (fun _ => iprop(True)) ∗
    spscConsumer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
    monoListIdxOwn γ.cur 0 (rev - W64 1) ∗ monoListIdxOwn γ.cur2 0 (rev - W64 1) ∗
    ⌜γ.cpl = cplCond sr o rev⌝)

/-- **The read-only fields of a `watchRequest`** at `l` (all but `rev` and `retc`), at the watch's
values: the context, the key and range end, the flags (`fragment` and `prevKV` false: the
contract's options), the filters' slice (nil: no filter). -/
def wrRO (l : Loc) (P : WsPrm GF) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.client.v3.watchRequest go!"ctx" l ↦□
      (interface.ok P.ctx : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.client.v3.watchRequest go!"key" l ↦□ P.key ∗
    structFieldRef go_etcd_io.etcd.client.v3.watchRequest go!"end" l ↦□ P.ed ∗
    structFieldRef go_etcd_io.etcd.client.v3.watchRequest go!"createdNotify" l ↦□ P.cn ∗
    structFieldRef go_etcd_io.etcd.client.v3.watchRequest go!"progressNotify" l ↦□ P.pn ∗
    structFieldRef go_etcd_io.etcd.client.v3.watchRequest go!"fragment" l ↦□ false ∗
    structFieldRef go_etcd_io.etcd.client.v3.watchRequest go!"watchBufLogEnabled" l ↦□ P.wbl ∗
    structFieldRef go_etcd_io.etcd.client.v3.watchRequest go!"filters" l ↦□ P.flt ∗
    P.flt ↦*□ ([] : List w32) ∗
    structFieldRef go_etcd_io.etcd.client.v3.watchRequest go!"prevKV" l ↦□ false)

instance wrRO_persistent (l : Loc) (P : WsPrm GF) : Persistent (wrRO l P) := by
  unfold wrRO; infer_instance

/-- **The cache's contract for the `k`th response `run` sends a substream** (persistent; K2e-7):
unless the watch promises no completeness (`cpl` false), the contract of the watch's prefix
(`watchRespOk`) from the second dispatch cursor's position `k` to `k + 1` (`γh2`). -/
def recvCmpl (V : WEnv GF) (P : WsPrm GF) (k : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (r : RespModel) : IProp GF :=
  iprop(⌜P.γ.cpl = false⌝ ∨ ∃ h2B h2A : w64, monoListIdxOwn P.γh2 k.toNat h2B ∗
    monoListIdxOwn P.γh2 (k.toNat + 1) h2A ∗ watchRespOk (EM := V.EM) P.o.key h2B h2A v r)

instance recvCmpl_persistent (V : WEnv GF) (P : WsPrm GF) (k : Int)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (recvCmpl V P k v r) := by
  unfold recvCmpl; infer_instance

/-- **A goroutine of the substream started at `recvc`'s position `k`** (persistent; D24): its
first response is a created one, with `run`'s half of the request's `rev` field. -/
def lifeStart (P : WsPrm GF) (k : Nat) : IProp GF := ghostMapElem P.γps k DFrac.discard true

/-- **`run` sent a response at `recvc`'s position `k` that is not a created one** (persistent;
D24): no goroutine of the substream started there. -/
def notStart (P : WsPrm GF) (k : Nat) : IProp GF := ghostMapElem P.γps k DFrac.discard false

instance lifeStart_persistent (P : WsPrm GF) (k : Nat) : Persistent (lifeStart (GF := GF) P k) := by
  unfold lifeStart; infer_instance

instance notStart_persistent (P : WsPrm GF) (k : Nat) : Persistent (notStart (GF := GF) P k) := by
  unfold notStart; infer_instance

theorem lifeStart_notStart (P : WsPrm GF) (k : Nat) :
    lifeStart (GF := GF) P k ∗ notStart P k ⊢ False := by
  unfold lifeStart notStart
  iintro ⟨H1, H2⟩
  ihave %H := ghostMapElem_agree _ _ _ _ _ _ $$ H1 H2
  cases H

/-- The position a substream's resume revision follows after a response `r`: its last event's
revision, or its header's revision. -/
abbrev resumePos (r : RespModel) : w64 := (r.events.getLast?.map EvModel.rev).getD r.hdrRev

/-- **A response's resume fact** (persistent; D24): unless the watch promises no completeness, a
create from just after the response's position (`resumePos`) is a start-read one
(`startOk ... true`: the server will deliver every event from it on). -/
def resumeF (V : WEnv GF) (P : WsPrm GF) (r : RespModel) : IProp GF :=
  iprop(⌜P.γ.cpl = false⌝ ∨ startOk V true (resumePos r + W64 1))

instance resumeF_persistent (V : WEnv GF) (P : WsPrm GF) (r : RespModel) :
    Persistent (resumeF V P r) := by
  unfold resumeF; infer_instance

/-- **A substream's resume revision** (persistent; D24): the request's `rev` field `rv` the
substream would be re-created from after a reconnect, at the dispatch cursor's position `hl` and
the second cursor's `c2`: at or above the watch's start (unless that is "now", `0`), above the
dispatch cursor (unless that is below `0`: no event yet of a watch from "now"), just past the
second cursor (when the watch promises completeness), and a create from it is one the server
accepts (`startOk`, start-read when the watch promises completeness). -/
def resumeOk (V : WEnv GF) (P : WsPrm GF) (rv hl c2 : w64) : IProp GF :=
  iprop(⌜(P.rev = W64 0 ∨ sint.Z P.rev ≤ sint.Z rv) ∧ (sint.Z hl < sint.Z rv ∨ sint.Z hl < 0) ∧
      (P.γ.cpl = true → c2 = rv - W64 1)⌝ ∗ startOk V (cplOf P) rv)

instance resumeOk_persistent (V : WEnv GF) (P : WsPrm GF) (rv hl c2 : w64) :
    Persistent (resumeOk V P rv hl c2) := by
  unfold resumeOk; infer_instance

/-- **A registration's base** (D24): the create's start revision `rr` and start-read flag `srr`,
and the dispatch cursor's position `hb` when the create was sent (the first create's: the watch's
start, its flag, `rev - 1`; a resumed create's: the resume revision, `cplOf`, the cursor then). -/
structure RegB where
  rr : w64
  srr : Bool
  hb : w64

/-- **A registration's base the contract allows** (pure; D24): at or above the watch's start
(unless that is "now"), above the cursor (unless no event yet), start-read and positive when the
watch promises completeness. -/
def regBOk (P : WsPrm GF) (B : RegB) : Prop :=
  (P.rev = W64 0 ∨ sint.Z P.rev ≤ sint.Z B.rr) ∧
    (sint.Z B.hb < sint.Z B.rr ∨ sint.Z B.hb < 0) ∧
    (P.γ.cpl = true → B.srr = true ∧ 1 ≤ sint.Z B.rr)

/-- The first create's base. -/
abbrev regB0 (P : WsPrm GF) : RegB := ⟨P.rev, P.sr, P.rev - W64 1⟩

theorem regB0_ok (pfx : GoString) (P : WsPrm GF) (hok : wsReqOk pfx P) (hc : P.γ.cpl = cplOf P) :
    regBOk P (regB0 P) := by
  obtain ⟨-, -, h0, -⟩ := hok
  refine ⟨Or.inr (Int.le_refl _), ?_, fun hcpl => ?_⟩
  · show sint.Z (P.rev - W64 1) < sint.Z P.rev ∨ sint.Z (P.rev - W64 1) < 0
    by_cases hz : P.rev = W64 0
    · right; rw [hz]; decide
    · left
      have : sint.Z P.rev ≠ 0 := fun h => hz (by word)
      have : sint.Z (P.rev - W64 1) = sint.Z P.rev - 1 := by word
      omega
  · rw [hc] at hcpl
    unfold cplOf cplCond at hcpl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcpl
    refine ⟨hcpl.1, ?_⟩
    have : sint.Z P.rev ≠ 0 := fun h => hcpl.2.2.2.2 (by word)
    show 1 ≤ sint.Z P.rev
    omega

/-- **The `k`th response `run` sends a substream** (`recvc`'s element) at `wr` (read-only): a
`WatchResponse` modelled by `r` (its events read-only, its header non-nil, `watchHdrOwn`: the
`Revision` owned for a response with events; no close error, no compaction, not canceled),
satisfying the contract from the dispatch cursor's position `k` to `k + 1` (`γhi`, a mono list
`run` extends); a created response has no events and `run`'s half of
the request's `rev` field (the substream writes it from then on); another is at no goroutine's
start (`notStart`, D24: a goroutine's first response is its create's) and gives its resume fact
(`resumeF`). Or the
substream's goroutine has stopped for good (`γx` set: what its `donec` publishes): `run`'s dispatch
to it after a failed one (the select took `donec`), which the stopped goroutine never receives. -/
def recvElem (V : WEnv GF) (P : WsPrm GF) (k : Int) (wr : Loc) : IProp GF :=
  iprop((∃ (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hiB hiA : w64),
    wr ↦□ v ∗
    ⌜v.Header' ≠ null ∧ v.closeErr' = GoInterface.nil ∧ v.CompactRevision' = r.compactRev ∧
      v.Canceled' = r.canceled ∧ v.Created' = r.created ∧ r.compactRev = W64 0 ∧
      r.canceled = false⌝ ∗
    eventsAt v.Events' r.events ∗ watchHdrOwn v.Header' r ∗
    monoListIdxOwn P.γhi k.toNat hiB ∗ monoListIdxOwn P.γhi (k.toNat + 1) hiA ∗
    rangeWatchRespOk (EM := V.EM) V.pfx P.o P.rev hiB hiA r ∗ recvCmpl V P k v r ∗
    (if r.created then
      iprop(⌜r.events = []⌝ ∗
        ∃ rv : w64, wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} rv)
    else iprop(notStart P k.toNat ∗ resumeF V P r))) ∨
    dghostVar P.γx DFrac.discard true)

/-- **A substream** `ws` of the watch `P` (persistent): its request's read-only fields
(`initReq`), its `recvc` field (read-only after `run` set it), the contract's SPSC channel `outc`,
`recvc` (a synchronous SPSC, `recvElem`), the request's context and `retc`, the request one of the
contract's. (D24: the `outc` field becomes `nil` when `waitCancelSubstreams` closes the channel, and
each lifetime of the goroutine has its own `donec`: owned fields, `LifePrm`.) -/
def wsIs (V : WEnv GF) (P : WsPrm GF) : IProp GF :=
  iprop(wrRO (wsF P.ws go!"initReq") P ∗
    wsF P.ws go!"recvc" ↦□ P.recvc ∗
    isSpsc P.γ.spsc P.outc (rangeWatchElem (EM := V.EM) P.γ V.pfx P.o P.rev)
      (fun _ => iprop(True)) ∗
    isSspsc P.γr P.recvc (recvElem V P) (fun _ => iprop(True)) ∗
    context.isContext P.ctx P.cs ∗
    isChanBag P.γret P.retc (retcP V P.o P.rev P.sr) ∗
    ⌜P.ws ≠ null ∧ wsReqOk V.pfx P ∧ P.γ.cpl = cplOf P⌝ ∗ startOk V P.sr P.rev)

instance wsIs_persistent (V : WEnv GF) (P : WsPrm GF) : Persistent (wsIs V P) := by
  unfold wsIs; infer_instance

/-! ## A goroutine's lifetime (D24) -/

/-- **A lifetime of a substream's goroutine** (D24; one per `go w.serveSubstream`): its `donec`
(and its names), the names of its deposit's flag (`γt`, set once the goroutine leaves what it holds
in the lifetime's invariant, `lifeSt`) and of `run`'s token for taking the deposit (`γk`), and the
generation of `resumec` it runs under (`gen`, `WgsPrm.γend`). -/
structure LifePrm where
  dc : Loc
  γdn : ChanNames
  γt : GName
  γk : GName
  gen : Nat

/-- **A `donec`** (its field's value, its names, the predicate its close publishes). -/
structure DnInfo (GF : BundledGFunctors) where
  dc : Loc
  γ : ChanNames
  Q : IProp GF

/-- **`run`'s half of a substream's `donec` field**, at `d`'s channel, and the channel (the
goroutine has the other half; `run` writes the field for each new lifetime). -/
def donecAt (ws : Loc) (d : DnInfo GF) : IProp GF :=
  iprop(wsF ws go!"donec" ↦{DFrac.own (1 : Qp).half} d.dc ∗ ownBroadcastChan d.dc d.γ d.Q .Unknown)

/-- An exclusive token. -/
def ownTok (γ : GName) : IProp GF := dghostVar γ (DFrac.own 1) ()

theorem ownTok_excl (γ : GName) : ownTok (GF := GF) γ ∗ ownTok γ ⊢ False := by
  unfold ownTok
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Hv
  exfalso
  obtain ⟨Hv, _⟩ := Hv
  revert Hv
  simp only [CMRA.Valid, DFrac.op_own]
  intro h
  have : (1 : Rat) + 1 ≤ 1 := h
  grind

/-- **The substream stopped for good** (persistent): its flag `γx`, its `closing` field `true` for
good. -/
def wsStopped (P : WsPrm GF) : IProp GF :=
  iprop(dghostVar P.γx DFrac.discard true ∗ wsF P.ws go!"closing" ↦□ true)

instance wsStopped_persistent (P : WsPrm GF) : Persistent (wsStopped (GF := GF) P) := by
  unfold wsStopped; infer_instance

/-- **The caller's resources of a watch** (`retc`'s content, before it is sent): the consumer's
side of `outc` at the start. -/
def retcRes (P : WsPrm GF) : IProp GF :=
  iprop(spscConsumer P.γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
    monoListIdxOwn P.γ.cur 0 (P.rev - W64 1) ∗ monoListIdxOwn P.γ.cur2 0 (P.rev - W64 1))

/-- **The second cursor's authority** (K2e-7), for `n` responses published: the cache's contract's
positions (`γ.cur2`, one more than the responses), unless the watch promises no completeness. -/
def cur2Auth (P : WsPrm GF) (n : Nat) : IProp GF :=
  iprop(⌜P.γ.cpl = false⌝ ∨ ∃ C2 : List w64, monoListAuthOwn P.γ.cur2 1 C2 ∗ ⌜C2.length = n + 1⌝)

/-- **The producer's side of `outc`**: the responses published (`sent`), the cursor's positions
`C` (one more than the responses: the contract's `γ.cur`, its authority). -/
def outcProd (P : WsPrm GF) : IProp GF :=
  iprop(∃ (sent : List go_etcd_io.etcd.client.v3.WatchResponse) (C : List w64),
    spscProducer P.γ.spsc sent ∗ monoListAuthOwn P.γ.cur 1 C ∗
    ⌜C.length = sent.length + 1⌝ ∗ cur2Auth P sent.length)

/-- **The second cursor's state at `serveSubstream`** (K2e-7), `n` responses published and the next
one to publish the `k`th received: the authority at positions ending at `cl2`, the second dispatch
cursor's position `k` (unless the watch promises no completeness). -/
def cur2Pos (P : WsPrm GF) (n k : Nat) : IProp GF :=
  iprop(⌜P.γ.cpl = false⌝ ∨ ∃ (C2 : List w64) (cl2 : w64), monoListAuthOwn P.γ.cur2 1 C2 ∗
    ⌜C2.length = n + 1 ∧ C2.getLast? = some cl2⌝ ∗ monoListIdxOwn P.γh2 k cl2)

theorem cur2Pos_auth (P : WsPrm GF) (n k : Nat) : cur2Pos P n k ⊢ cur2Auth P n := by
  unfold cur2Pos cur2Auth
  iintro (%H | ⟨%C2, %cl2, Ha, %H, -⟩)
  · ileft; ipureintro; exact H
  · iright; iexists C2; iframe Ha; ipureintro; exact H.1

/-! ## The gRPC watch stream's channels -/

/-- **What `respc` carries** (`serveWatchClient` to `run`; the SPSC element `k`, for the gRPC
stream `γs` with the server's content `Dn`): the stream's `k`th response, decoded and owned
(`watchRespRecv`), its content, and the down queue's prefix it ends. -/
def respcElem (γs : StreamNames) (Dn : Nat → v3rpc.WatchRespM → IProp GF) (k : Int) (p : Loc) :
    IProp GF :=
  iprop(∃ (m : v3rpc.WatchRespM) (L : List v3rpc.WatchRespM),
    v3rpc.watchRespRecv p m ∗ Dn k.toNat m ∗ v3rpc.downLbW γs (L ++ [m]) ∗ ⌜L.length = k.toNat⌝)

instance streamNames_countable : Pos.Countable StreamNames :=
  .ofInjective (fun s => Pos.Countable.encode (s.up, s.upRcv, s.down, s.upEnd, s.downRcv, s.downEnd,
    s.aux))
    (by rintro ⟨a, b, c, d, e, f, g⟩ ⟨a', b', c', d', e', f', g'⟩ h; have h := Pos.encode_inj h;
        simp_all)

/-- **An epoch of `run`** (D24): the gRPC stream it opened, the first position of `respc` its
responses take, the name of its count of responses forwarded (a mono nat, `serveWatchClient`'s). -/
abbrev EpInfo := StreamNames × Nat × GName

/-- **What `respc` carries, across reconnections** (D24): the `k`th element was forwarded from the
gRPC stream of some epoch `e` of `run` (`γep`), from its first position `b` on, while its count was
at `k` (the count's lower bound `k + 1`: the epoch had not ended), and is that stream's `(k - b)`th
response (`respcElem`, its content the watch stream's `watchDn`). -/
def respcE (V : WEnv GF) (γep : GName) (k : Int) (p : Loc) : IProp GF :=
  iprop(∃ (e b : Nat) (γs : StreamNames) (γc : GName),
    monoListIdxOwn γep e ((γs, b, γc) : EpInfo) ∗ monoNatLbOwn γc (k.toNat + 1) ∗ ⌜b ≤ k.toNat⌝ ∗
    respcElem γs (v3rpc.watchDn γs V.R.γ V.R.cid V.R.mid) ((k.toNat - b : Nat) : Int) p)

/-- **`respc`'s producer side, handed back** (D24; with the stream's receive error on `errc`): the
epoch the forwarder served, its count at the responses sent. -/
def prodBack (γr : SpscNames) (γep : GName) : IProp GF :=
  iprop(∃ (e b : Nat) (γs : StreamNames) (γc : GName) (sent : List Loc),
    monoListIdxOwn γep e ((γs, b, γc) : EpInfo) ∗ sspscProducer γr sent ∗
    monoNatAuthOwn γc 1 sent.length ∗ ⌜b ≤ sent.length⌝)

/-- **What `errc` carries** (`serveWatchClient`'s receive error; a bag): a stream error or
`io.EOF`, which grpc's `status` accepts, and (D24) `respc`'s producer side, handed back to `run`
for the next stream. -/
def errP (γr : SpscNames) (γep : GName) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∗ (cliStreamErr err ∨ eofIs err) ∗ statusErrOk err ∗
    prodBack γr γep)

/-- **What `donec`'s closing publishes**: `run` stopped with the close error `e` (read-only for
good), one grpc's `status` accepts. -/
def closeErrPub (wgs : Loc) : IProp GF :=
  iprop(∃ e : GoInterface, wgsF wgs go!"closeErr" ↦□ e ∗ statusErrOk e)

instance closeErrPub_persistent (wgs : Loc) : Persistent (closeErrPub (GF := GF) wgs) := by
  unfold closeErrPub; infer_instance

/-- **What `reqc` carries** (a bag): a `*watchRequest`, read-only, of a watch of the contract, its
`retc` a bag carrying its channel (`retcP`); or (unit W-K) a `*progressRequest`
(`RequestProgress`'s). -/
def reqP (V : WEnv GF) (v : GoInterface) : IProp GF :=
  iprop((∃ (wr : Loc) (P : WsPrm GF),
    ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watchRequest.ty) #wr ∧
      wr ≠ null⌝ ∗
    wrRO wr P ∗ wrF wr go!"rev" ↦□ P.rev ∗ wrF wr go!"retc" ↦□ P.retc ∗
    context.isContext P.ctx P.cs ∗ isChanBag P.γret P.retc (retcP V P.o P.rev P.sr) ∗
    ⌜wsReqOk V.pfx P⌝ ∗ startOk V P.sr P.rev) ∨
    ∃ pr : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.progressRequest.ty) #pr⌝)

instance reqP_persistent (V : WEnv GF) (v : GoInterface) : Persistent (reqP V v) := by
  unfold reqP; infer_instance

/-- **What a goroutine stopping for good leaves** (D24: in its lifetime's invariant, `lifeSt`):
the `outc` field and the producer's side of `outc` (or the field `nil`, the channel closed by
`waitCancelSubstreams` once the watch's context was done), its `retc` field (with the caller's
resources if it never sent its channel), its part of the request's `rev` field with the facts of
its value as a resume revision (a reconnection re-creates the stopped substream from it), its half
of the `donec` field. -/
def stopBody (V : WEnv GF) (P : WsPrm GF) : IProp GF :=
  iprop(∃ (rc : Loc) (q : Qp) (nr : w64) (dc : Loc),
    (wsF P.ws go!"outc" ↦ P.outc ∗ outcProd P ∨
      wsF P.ws go!"outc" ↦ null ∗ context.ContextClosed P.cs.Done_gn) ∗
    wsReqF P.ws go!"retc" ↦ rc ∗ (⌜rc = null⌝ ∨ ⌜rc = P.retc⌝ ∗ retcRes P) ∗
    wsReqF P.ws go!"rev" ↦{DFrac.own q} nr ∗ (∃ hl c2 : w64, resumeOk V P nr hl c2) ∗
    wsF P.ws go!"donec" ↦{DFrac.own (1 : Qp).half} dc)

/-- **A substream that stopped** (not to resume), with what its goroutine left (`stopBody`;
`closeSubstream`'s precondition). -/
def closingBody (V : WEnv GF) (ws : Loc) : IProp GF :=
  iprop(∃ (P : WsPrm GF), ⌜P.ws = ws⌝ ∗ wsIs V P ∗ stopBody V P)

/-- **A gRPC watch stream's values** (fixed by `newWatcherGRPCStream`): its owner and context key,
its context (`ctx`, the `*cancelCtx` over `valCtx{inctx}`, never done until cancelled, `cd`) and
`cancel`, its channels and their names, its wait group's. -/
structure WgsPrm (GF : BundledGFunctors) where
  wgs : Loc
  w : Loc
  ctx : GoInterfaceOk
  cd : context.ContextDesc (IProp GF)
  γctx : context.ContextNames
  cancel : GoFunc
  ckey : GoString
  reqc : Loc
  γreq : ChanNames
  respc : Loc
  donec : Loc
  γdone : ChanNames
  errc : Loc
  γerr : ChanNames
  closingc : Loc
  γclosing : ChanNames
  /-- the stream's substreams, a ghost map with exclusive elements (`closingP`'s membership) -/
  γws : GName
  /-- (D24) `respc`'s SPSC names (its element `respcE`: tagged by the gRPC stream it came from) -/
  γr : SpscNames
  /-- (D24) the epochs of `run`: a mono list of the gRPC streams it opened, each with its first
  position on `respc` and the name of its count of responses forwarded (`EpInfo`) -/
  γep : GName
  /-- (D24) the generations of `resumec`: a mono nat, `run`'s authority at the current one `n`
  (`resumec` closed publishes `n + 1`, `newWatchClient`) -/
  γend : GName

/-- **What `closingc` carries** (a bag): a substream of this stream that stopped, by its
membership token (`G.γws`, one per substream `run` made: so `run` knows the message is about one of
its own). D24: what the goroutine left is in its lifetime's invariant (`lifeSt`), which `run`
opens with its token; the full membership token says the lifetime is no longer running. -/
def closingP (V : WEnv GF) (G : WgsPrm GF) (ws : Loc) : IProp GF :=
  iprop(ghostMapElem G.γws ws (DFrac.own 1) ())

/-- **A gRPC watch stream** `G.wgs` of the watcher `G.w` (persistent): the call options and the
server's facts (`watchSrvFacts`, as the watcher's), its read-only fields, its
context and `cancel` (callable from anywhere), its channels (`reqc`, `errc`, `closingc` bags;
`donec` publishing `closeErrPub`). -/
def isWGS (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) : IProp GF :=
  iprop(⌜G.wgs ≠ null⌝ ∗ (∃ vs : List GoInterface, callSl ↦*□ vs ∗ callOptsOk vs) ∗
    watchSrvFacts V ∗ ⌜V.lg ≠ null⌝ ∗
    wgsF G.wgs go!"owner" ↦□ G.w ∗ wgsF G.wgs go!"remote" ↦□ wcIface V.wc ∗
    wgsF G.wgs go!"callOpts" ↦□ callSl ∗
    wgsF G.wgs go!"ctx" ↦□ (interface.ok G.ctx : GoInterface) ∗
    wgsF G.wgs go!"ctxKey" ↦□ G.ckey ∗ wgsF G.wgs go!"cancel" ↦□ G.cancel ∗
    wgsF G.wgs go!"reqc" ↦□ G.reqc ∗ wgsF G.wgs go!"respc" ↦□ G.respc ∗
    wgsF G.wgs go!"donec" ↦□ G.donec ∗ wgsF G.wgs go!"errc" ↦□ G.errc ∗
    wgsF G.wgs go!"closingc" ↦□ G.closingc ∗ wgsF G.wgs go!"lg" ↦□ V.lg ∗
    context.isContext G.ctx G.cd ∗ context.cancelSpec G.cancel G.γctx iprop(True) ∗
    isChanBag G.γreq G.reqc (reqP V) ∗ isChanBag G.γerr G.errc (errP G.γr G.γep) ∗
    isChanBag G.γclosing G.closingc (closingP V G) ∗
    ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Unknown ∗
    isSspsc G.γr G.respc (respcE V G.γep) (fun _ => iprop(False)))

instance isWGS_persistent (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) :
    Persistent (isWGS V G callSl) := by
  unfold isWGS; infer_instance

/-! ## The watcher -/

/-- **What the watcher's lock guards**: the streams map, `nil` once closed, otherwise a map from
context keys to gRPC watch streams (`isWGS`). -/
def watcherMu (V : WEnv GF) (w : Loc) (callSl : GoSlice) : IProp GF :=
  iprop(∃ m : Loc, watcherF w go!"streams" ↦ m ∗
    (⌜m = null⌝ ∨ ∃ M : GMap GoString Loc, ownMap m (DFrac.own 1) M ∗
      [∗map] _k ↦ wgs ∈ M, ∃ G : WgsPrm GF, ⌜G.wgs = wgs ∧ G.w = w⌝ ∗ isWGS V G callSl))

/-- **The watcher `w`** (persistent; the file header): its read-only fields (the stub, the call
options, the logger), its lock, the server's and the transport's facts. -/
def isClientWatcher (V : WEnv GF) (w : Loc) : IProp GF :=
  iprop(∃ (callSl : GoSlice) (vs : List GoInterface),
    ⌜w ≠ null⌝ ∗
    watcherF w go!"remote" ↦□ wcIface V.wc ∗ watcherF w go!"callOpts" ↦□ callSl ∗
    callSl ↦*□ vs ∗ callOptsOk vs ∗ watcherF w go!"lg" ↦□ V.lg ∗
    sync.isMutex (watcherF w go!"mu") (watcherMu V w callSl) ∗
    watchSrvFacts V ∗ ⌜V.lg ≠ null ∧ threadBound GF ≤ 2 ^ 31⌝)

instance isClientWatcher_persistent (V : WEnv GF) (w : Loc) : Persistent (isClientWatcher V w) := by
  unfold isClientWatcher; infer_instance

/-! ## The substreams' bookkeeping (what `run`'s helpers take) -/

/-- An owned slice with its capacity (what `append` takes). -/
def sliceOwn (s : GoSlice) (l : List Loc) : IProp GF :=
  iprop(s ↦* l ∗ ownSliceCap Loc s (DFrac.own 1))

/-- `addSubstream` refuses a created response: the invalid watch id, or canceled with a reason. -/
abbrev addFails (id : w64) (ca : Bool) (rs : GoString) : Prop :=
  id = W64 (-1) ∨ (ca = true ∧ rs ≠ [])

/-- `closeSubstream`'s scan of `resuming`: the first `ws` set to nil. -/
def nilOut (l : List Loc) (ws : Loc) : List Loc :=
  match l.findIdx? (· = ws) with
  | some i => l.set i null
  | none => l

/-- **The current lifetime's `donec`, for a send** (D24): `run`'s half of the field at `d`, and that
the close of `d` with `run`'s generation authority at `n` (`γend`) says the substream stopped for
good (a lifetime of the current generation ends only so). -/
def dnCap (P : WsPrm GF) (d : DnInfo GF) (γend : GName) (n : Nat) : IProp GF :=
  iprop(donecAt P.ws d ∗
    □ (d.Q -∗ monoNatAuthOwn γend 1 n -∗ dghostVar P.γx DFrac.discard true))

/-- **The right to send the response `wr` to the substream of `P`**: `recvc`'s producer side at
`sent` with `wr`'s content as its next element, the current lifetime's `donec` (`dnCap`). -/
def sendCap1 (V : WEnv GF) (P : WsPrm GF) (sent : List Loc) (wr : Loc) (d : DnInfo GF)
    (γend : GName) (n : Nat) : IProp GF :=
  iprop(wsIs V P ∗ sspscProducer P.γr sent ∗ recvElem V P sent.length wr ∗ dnCap P d γend n)

/-- **The right to send `run`'s next response to the substream of `P`** (`recvc`'s producer side at
`sent`), with the response's content for any location `wr` it will be at (`Ψ wr`: the facts about
the new `*WatchResponse`, which `dispatchEvent` allocates), the current lifetime's `donec`. -/
def sendCap (V : WEnv GF) (P : WsPrm GF) (sent : List Loc) (Ψ : Loc → IProp GF) (d : DnInfo GF)
    (γend : GName) (n : Nat) : IProp GF :=
  iprop(wsIs V P ∗ sspscProducer P.γr sent ∗ (∀ wr : Loc, Ψ wr -∗ recvElem V P sent.length wr) ∗
    dnCap P d γend n)

/-- After a successful send of `wr`: the producer's side advanced, the `donec` back. -/
def sendDone (P : WsPrm GF) (sent : List Loc) (wr : Loc) (d : DnInfo GF) (γend : GName)
    (n : Nat) : IProp GF :=
  iprop(sspscProducer P.γr (sent ++ [wr]) ∗ dnCap P d γend n)

/-- After a failed send of `wr` (the substream's goroutine stopped): the producer's side as it was,
`wr`'s content back, and the goroutine's stop published (`γx`, from its closed `donec`). -/
def sendFail (V : WEnv GF) (P : WsPrm GF) (sent : List Loc) (wr : Loc) (d : DnInfo GF)
    (γend : GName) (n : Nat) : IProp GF :=
  iprop(sspscProducer P.γr sent ∗ recvElem V P sent.length wr ∗
    dghostVar P.γx DFrac.discard true ∗ dnCap P d γend n)

/-- **The right to close the substream `ws`'s `recvc`** (its producer side). -/
def recvcCloser (V : WEnv GF) (ws : Loc) : IProp GF :=
  iprop(∃ (P : WsPrm GF) (sent : List Loc), ⌜P.ws = ws⌝ ∗ wsIs V P ∗ sspscProducer P.γr sent)

/-- The `WatchResponse` `dispatchEvent` makes of a response holding `m` whose header pointer is
`h` and events slice `sl`. -/
def wrOf (m : v3rpc.WatchRespM) (h : Loc) (sl : GoSlice) : go_etcd_io.etcd.client.v3.WatchResponse :=
  { Header' := h, Events' := sl, CompactRevision' := m.compactRev, Canceled' := m.canceled,
    Created' := m.created, closeErr' := GoInterface.nil, CancelReason' := m.cancelReason }

/-- `dispatchEvent` broadcasts a response (`IsProgressNotify` with id `-1`). -/
abbrev isBroadcast (m : v3rpc.WatchRespM) : Prop :=
  m.evs = [] ∧ m.canceled = false ∧ m.created = false ∧ m.compactRev = W64 0 ∧
    m.hdr.revision ≠ W64 0 ∧ m.watchId = W64 (-1)

/-- **A response's fields `dispatchEvent` reads** at `p` (fractions `dq`), holding `m`, its header
pointer `h` (non-nil) and events slice `sl`. -/
def respFields (p : Loc) (dq : DFrac) (m : v3rpc.WatchRespM) (h : Loc) (sl : GoSlice) : IProp GF :=
  iprop(⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.WatchResponse go!"Header" p ↦{dq} h ∗
    structFieldRef etcdserverpb.WatchResponse go!"WatchId" p ↦{dq} m.watchId ∗
    structFieldRef etcdserverpb.WatchResponse go!"Created" p ↦{dq} m.created ∗
    structFieldRef etcdserverpb.WatchResponse go!"Canceled" p ↦{dq} m.canceled ∗
    structFieldRef etcdserverpb.WatchResponse go!"CompactRevision" p ↦{dq} m.compactRev ∗
    structFieldRef etcdserverpb.WatchResponse go!"CancelReason" p ↦{dq} m.cancelReason ∗
    structFieldRef etcdserverpb.WatchResponse go!"Fragment" p ↦{dq} m.fragment ∗
    structFieldRef etcdserverpb.WatchResponse go!"Events" p ↦{dq} sl)

/-! ## The substream's buffer logger -/

/-- What the substream's buffer logger's closure reads (`w.lg.Info` of the request's key, range
end and revision and the buffer's length): the request's `rev` field (at the fraction `q`, holding
`rv`) and the `buf` field (`b`). -/
def wsLogA (ws : Loc) (x : Qp × w64 × GoSlice) : IProp GF :=
  iprop(wsReqF ws go!"rev" ↦{DFrac.own x.1} x.2.1 ∗ wsF ws go!"buf" ↦ x.2.2)

/-- **A block logger** `bl` (persistent) whose `now` returns a time and whose `logFunc` keeps
`A x` for any `x`: its fields, its lock (guarding its counters). -/
def isBlockLogger {α : Type} (bl : Loc) (A : α → IProp GF) : IProp GF :=
  iprop(∃ (nowf lf : GoFunc) (iv th : _root_.Perennial.time.Duration),
    ⌜bl ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"interval" bl ↦□ iv ∗
    structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"threshold" bl ↦□ th ∗
    structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"now" bl ↦□ nowf ∗
    structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"logFunc" bl ↦□ lf ∗
    (□ ∀ Φ : val → IProp GF, ▷ (∀ t : _root_.Perennial.time.Time, Φ #t) -∗
      WP (App (Val #nowf) (Val #())) {{ Φ }}) ∗
    (□ ∀ (x : α) (n : w64) (d1 d2 : _root_.Perennial.time.Duration),
      {{ A x }} (App (App (App (Val #lf) (Val #n)) (Val #d1)) (Val #d2)) {{ RET #(); A x }}) ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"mu" bl)
      iprop(∃ (t : _root_.Perennial.time.Time) (n : w64) (d : _root_.Perennial.time.Duration),
        structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"lastLogTime" bl ↦ t ∗
        structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"eventCount" bl ↦ n ∗
        structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"timeWaiting" bl ↦ d))

instance isBlockLogger_persistent {α : Type} (bl : Loc) (A : α → IProp GF) :
    Persistent (isBlockLogger bl A) := by
  unfold isBlockLogger; infer_instance

/-- The substream's buffer logger: none, or a block logger over its fields (`wsLogA`). -/
def bufLogOk (ws bl : Loc) : IProp GF :=
  iprop(⌜bl = null⌝ ∨ isBlockLogger bl (wsLogA (GF := GF) ws))

instance bufLogOk_persistent (ws bl : Loc) : Persistent (bufLogOk (GF := GF) ws bl) := by
  unfold bufLogOk; infer_instance

/-! ## The wait group of a gRPC watch stream's substreams -/

/-- The right to call `Done` once on the stream's wait group (a running token; the `Done` gives
back a thread token, `InvWatchWg.lean`). -/
def wgDone (wgs : Loc) : IProp GF := wgsWgDone (wgsF wgs go!"wg")

/-- The right to `Add(1)` to and `Wait` on the stream's wait group (`run`'s, under the thread
bound `threadBound GF ≤ 2^31`; each `Add(1)` deposits the caller's thread token,
`InvWatchWg.lean`). -/
def wgAdder (wgs : Loc) : IProp GF := wgsWgAdder (wgsF wgs go!"wg")

/-! ## A lifetime's state and deposit (D24) -/

/-- **A received response, live** (`recvElem`'s first disjunct): its value, read-only, with its
content and the contract's positions around it. -/
def recvLive (V : WEnv GF) (P : WsPrm GF) (k : Int) (wr : Loc) : IProp GF :=
  iprop(∃ (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hiB hiA : w64),
    wr ↦□ v ∗
    ⌜v.Header' ≠ null ∧ v.closeErr' = GoInterface.nil ∧ v.CompactRevision' = r.compactRev ∧
      v.Canceled' = r.canceled ∧ v.Created' = r.created ∧ r.compactRev = W64 0 ∧
      r.canceled = false⌝ ∗
    eventsAt v.Events' r.events ∗ watchHdrOwn v.Header' r ∗
    monoListIdxOwn P.γhi k.toNat hiB ∗ monoListIdxOwn P.γhi (k.toNat + 1) hiA ∗
    rangeWatchRespOk (EM := V.EM) V.pfx P.o P.rev hiB hiA r ∗ recvCmpl V P k v r ∗
    (if r.created then
      iprop(⌜r.events = []⌝ ∗
        ∃ rv : w64, wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} rv)
    else iprop(notStart P k.toNat ∗ resumeF V P r)))

/-- **The dispatch cursors do not move from `recvc`'s position `a` to `b`** (persistent; D24): the
responses between were created ones the goroutine skipped (a resumed create keeps both cursors). -/
def chainE (P : WsPrm GF) (a b : Nat) : IProp GF :=
  iprop(⌜a ≤ b⌝ ∗ (∃ c : w64, monoListIdxOwn P.γhi a c ∗ monoListIdxOwn P.γhi b c) ∗
    (⌜P.γ.cpl = false⌝ ∨ ∃ c : w64, monoListIdxOwn P.γh2 a c ∗ monoListIdxOwn P.γh2 b c))

instance chainE_persistent (P : WsPrm GF) (a b : Nat) : Persistent (chainE (GF := GF) P a b) := by
  unfold chainE; infer_instance

/-- **The buffer's entries** from `recvc`'s position `a` to `n` (the next to receive): each entry a
received response at its position (`recvLive`), the positions between them skipped (`chainE`). -/
def bufE (V : WEnv GF) (P : WsPrm GF) : Nat → List (Nat × Loc) → Nat → IProp GF
  | a, [], n => chainE P a n
  | a, x :: rest, n => iprop(chainE P a x.1 ∗ recvLive V P (x.1 : Int) x.2 ∗ bufE V P (x.1 + 1) rest n)

/-- **A goroutine's state** (D24: `serveSubstream`'s loop, and what a lifetime hands to the next),
its lifetime started at `recvc`'s position `k0` with the request's `rev` field at `rv0`, `rcv`
received, its resume revision `nr`: `recvc`'s consumer, `outc`'s producer and cursor (`γ.cur`, its
last position `cl` the dispatch cursor's at `p0`, the position after the last response published),
the buffer (`bufE`), the request's `rev` field (half at `rv0` until the lifetime's first response,
then whole at `nr`), the resume revision's facts (`resumeOk`), the `retc` field (the caller's
resources until the first response ever, the request's `rev` still the watch's start and the
cursor's first position its), the buffer's wait start. -/
def wsRun (V : WEnv GF) (P : WsPrm GF) (k0 : Nat) (rv0 : w64) (rcv : List Loc) (nr : w64) :
    IProp GF :=
  iprop(∃ (sent : List go_etcd_io.etcd.client.v3.WatchResponse) (C : List w64)
      (bq : List (Nat × Loc)) (b : GoSlice) (rcf : Loc) (t : _root_.Perennial.time.Time) (cl : w64)
      (p0 : Nat),
    sspscConsumer P.γr rcv ∗ ⌜k0 ≤ rcv.length⌝ ∗
    spscProducer P.γ.spsc sent ∗ monoListAuthOwn P.γ.cur 1 C ∗
    ⌜C.length = sent.length + 1 ∧ C.getLast? = some cl⌝ ∗
    monoListIdxOwn P.γhi p0 cl ∗ cur2Pos P sent.length p0 ∗
    wsF P.ws go!"buf" ↦ b ∗ sliceOwn b (bq.map Prod.snd) ∗ bufE V P p0 bq rcv.length ∗
    ((⌜rcv.length = k0 ∧ nr = rv0⌝ ∗ wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} rv0) ∨
      (⌜rcv.length ≠ k0⌝ ∗ wsReqF P.ws go!"rev" ↦ nr)) ∗
    (∃ hl c2 : w64, monoListIdxOwn P.γhi rcv.length hl ∗
      (⌜P.γ.cpl = false⌝ ∨ monoListIdxOwn P.γh2 rcv.length c2) ∗ resumeOk V P nr hl c2) ∗
    wsReqF P.ws go!"retc" ↦ rcf ∗
    ((⌜rcv = [] ∧ rcf = P.retc ∧ nr = P.rev⌝ ∗ retcRes P ∗ monoListIdxOwn P.γhi 0 (P.rev - W64 1)) ∨
      ⌜rcv ≠ [] ∧ rcf = null⌝) ∗
    wsF P.ws go!"bufWaitStartTime" ↦ t)

/-- **What a goroutine resumed leaves** (D24: on `resumec`, in its lifetime's invariant): its state
(`wsRun`), its fields (`closing` `false`, the buffer logger, `outc`, its half of `donec`), its flag
`γx` (`false`), its membership token (whole). -/
def resumeBody (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) : IProp GF :=
  iprop(∃ (k0 : Nat) (rv0 : w64) (rcv : List Loc) (nr : w64) (bl dc : Loc),
    wsRun V P k0 rv0 rcv nr ∗ lifeStart P k0 ∗ wsF P.ws go!"closing" ↦ false ∗
    wsF P.ws go!"bufLogger" ↦ bl ∗ bufLogOk P.ws bl ∗ wsF P.ws go!"outc" ↦ P.outc ∗
    wsF P.ws go!"donec" ↦{DFrac.own (1 : Qp).half} dc ∗
    dghostVar P.γx (DFrac.own 1) false ∗ ghostMapElem G.γws P.ws (DFrac.own 1) ())

/-- **What `waitCancelSubstreams` lends a resuming substream's goroutine** (D24): its values and what
the substream's last goroutine left on `resumec` (`resumeBody`: the goroutine may close the
substream if its watch's context is done), or what a goroutine stopped for good left
(`stopBody`, whose `outc` the goroutine closes if the context is done). -/
def wcIn (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) : IProp GF :=
  iprop(wsIs V P ∗ (resumeBody V G P ∨ (wsStopped P ∗ stopBody V P)))

/-- **What a resuming substream's goroutine of `waitCancelSubstreams` gives back**: the resumed
state unchanged (`stopc` closed first), or the substream stopped for good (closed by the goroutine
once the watch's context is done, its membership token posted on `closingc`, or stopped before). -/
def wcOut (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) : IProp GF :=
  iprop(resumeBody V G P ∨ (wsStopped P ∗ stopBody V P))

/-- The namespace of the lifetimes' invariants. -/
abbrev lifeN : Namespace := nroot.@"wsLife"

/-- **A lifetime's invariant** (D24): running (half its flag `γt`, `false`, the goroutine has the
other; half the membership token), or the goroutine's deposit (`γt` set for good): stopped for good
(`wsStopped`, `stopBody`) or resumed (`resumec`'s generation `gen` ended, `resumeBody`), until `run`
takes it with its token `γk`. -/
def lifeSt (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) (L : LifePrm) : IProp GF :=
  iprop((dghostVar L.γt (DFrac.own (1 : Qp).half) false ∗
      ghostMapElem G.γws P.ws (DFrac.own (1 : Qp).half) ()) ∨
    (dghostVar L.γt DFrac.discard true ∗
      ((wsStopped P ∗ (stopBody V P ∨ ownTok L.γk)) ∨
       (monoNatLbOwn G.γend (L.gen + 1) ∗ (resumeBody V G P ∨ ownTok L.γk)))))

abbrev lifeInvIs (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) (L : LifePrm) : IProp GF :=
  inv lifeN (lifeSt V G P L)

/-- **What a lifetime's `donec` publishes** (persistent): its invariant, its deposit made (`γt`),
and how it ended: stopped for good, or resumed (its generation ended). -/
def lifeQ (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) (L : LifePrm) : IProp GF :=
  iprop(lifeInvIs V G P L ∗ dghostVar L.γt DFrac.discard true ∗
    (wsStopped P ∨ monoNatLbOwn G.γend (L.gen + 1)))

instance lifeQ_persistent (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) (L : LifePrm) :
    Persistent (lifeQ V G P L) := by
  unfold lifeQ; infer_instance

/-- A lifetime's `donec`. -/
abbrev lifeDn (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) (L : LifePrm) : DnInfo GF :=
  ⟨L.dc, L.γdn, lifeQ V G P L⟩

/-- **A lifetime of the current generation `n` ended for good** (`dnCap`'s fact): its close's
generation case contradicts `run`'s authority at `n`. -/
theorem lifeQ_cur (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) (L : LifePrm) (n : Nat)
    (hn : L.gen = n) :
    ⊢ □ (lifeQ V G P L -∗ monoNatAuthOwn G.γend 1 n -∗ dghostVar P.γx DFrac.discard true) := by
  iintro !> HQ Ha
  unfold lifeQ wsStopped
  icases HQ with ⟨-, -, (⟨#Hx, -⟩ | #Hlb)⟩
  · iexact Hx
  · ihave %Hv := monoNatLbOwn_valid _ _ _ _ $$ Ha Hlb
    exfalso; omega

end defs

end client
end EtcdGrove
end Perennial
