/-
# The client watcher's internals (batch 1b): vocabulary of `watch.go`'s internal specs

Not part of the client's API: the predicates the specs of `watch.go`'s internal functions
(`watchGRPCStream.*`, `watcher.newWatcherGRPCStream`, `watcher.closeStream`, `valCtx.*`, the
`toPB`s) are stated over, so that each of those functions keeps a spec (they were all proved:
`specs-ref/Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__*.lean`). Only `watch.go`'s own proofs
import this module; the client-facing statements (`ApiWatch.lean`) mention none of it.

## The goroutines and who owns what (the intended realization)

A `*watchGRPCStream` `s` (one per context key of a `*watcher`) runs `run` (the only sender on the
gRPC stream and the owner of `substreams`, `resuming`, `closeErr`, `resumec`), `serveWatchClient`
(the only receiver, forwarding each response on `respc`, or its error on `errc`), and one
`serveSubstream` per watch (`*watcherStream` `ws`), fed by `run` on `ws.recvc` with responses whose
`watchStep` facts `run` has established (from `wireWatchRecv_recv`'s `wireStep`, the registration
of the response's id being `ws`'s), buffering them in `ws.buf` and delivering them on `ws.outc`,
the channel `watchChAt` is the consumer of.

* `wgsAt s w γ p` (persistent; `p` the principal the member authenticates the stream as, from its
  context's metadata, `ctxPrin`; the internal specs name it `who`): `s`'s read-only fields (its watcher `w`, the stub, the call
  options, the context `ctx` (a `WithCancel` over a `valCtx`: never done until `cancel`), `ctxKey`,
  `cancel`, the channels, the logger) and the invariants of its channels: `reqc` (a `Watch`'s
  `*watchRequest`, with its `retc`'s protocol: the channel received on it comes with its
  consumer's `watchChAt`; or a `*progressRequest`), `respc` and `errc` (`serveWatchClient`'s
  responses with their `wireStep` facts and its error), `closingc` (a stopped substream, `wsClosed`),
  `donec` (closed once, by `closeStream`, publishing `closeErr` read-only: what `Watch` and
  `RequestProgress` read after `<-donec`), the wait group `wg` backed by thread tokens (one deposited
  per goroutine added, `Done` takes it back).
* `wgsRun s γ who r` (exclusive, `run`'s): the fields `substreams`, `resuming`, `closeErr` at the
  model `r` (`RunM`); for each substream in them, its `wsAt` and `run`'s side of it: the send right
  on its `recvc`, the right to join its goroutine (`<-ws.donec`) or, once joined (`r.joined`), its
  `wsOwn`; the ghost tie between the current stream's registrations and the substreams (which id
  is which `ws`, each registration's position the substream's); the right to close `donec`.
* `wgsSend s γ who wc` (exclusive, `run`'s): the sending half of the current gRPC stream
  (`wireWatchSend`), tied to `s`. `wgsRecv s γ who wc` (exclusive, `serveWatchClient`'s): its
  receiving half (`wireWatchRecv`) and the right to send on `respc`/`errc`.
* `wsAt ws s γ who w` (persistent): the substream's read-only fields: `initReq` but its `rev` and
  `retc` (`initReqAt`), `outc`, `recvc`; its watch `w`.
* `wsOwn ws s γ who q` (exclusive): its mutable fields (`id`, `closing`, `donec`, `buf`,
  `initReq.rev` (its position's `done + 1`), `initReq.retc`, `bufLogger`, `bufWaitStartTime`), at
  the model `q` (`WsM`), with the producer half of its consumer's contract: every buffered response
  with its `watchStep` facts at the positions it will be delivered at.
* `wsServe ws s γ who resumec` (exclusive): what a `serveSubstream` goroutine holds besides
  `wsOwn`: the receive side of `recvc`, the `Done` right on `s.wg` (a deposited thread token), the
  generation's `resumec`.
* `wsClosed ws s γ who q`: a stopped substream as `closingc` carries it (`wsOwn` at `q`, `closing`
  set, and what `closeSubstream` needs to end its consumer's channel).
* `wsCloser ws s γ who m`: the right to send the final error response `m` on `ws.outc` and close it
  (`sendCloseSubstream`'s).
* `deliverOk s γ who tgt m` (persistent): what the substream(s) `m` goes to may do with it:
  `tgt = none` (a broadcast progress): for every registered substream, a `watchStep` at its
  position (a substream in `r.subs` never had its cancel sent: `run` cancels only ids with no
  substream, after `closeSubstream` or for an unknown id, so `wireStep`'s exemption never meets
  one); `tgt = some id`: if no substream is registered as `id` (a refused create's `-1`, a
  canceled or stale id), nothing; else, for that substream, a `Created` (forwarded to the
  consumer only while `retc` is pending and with `createdNotify`, else dropped: a watch without
  `createdNotify`, a resumed substream) or a `watchStep` at its position (the ghost tie).
* **The tie** between the current stream's registrations and the substreams is a refinement, not
  an equality: a substream's channel position is its registration's, or weaker (`done = none`
  where the registration has one: a `rev = 0` watch resumed from `H`; `prevLoose` kept true, as
  every re-registration reopens the member's `PrevKv` window); an ended substream (its
  error buffered or delivered) delivers nothing more, whatever its registration says (a resume
  may re-register it from a later header).
* **Who writes what of a substream**: `ws.id` is `run`'s (in `wgsRun`'s per-substream part:
  `addSubstream`, the `Canceled` branch and `newWatchClient` write it while the goroutine runs);
  `ws.initReq.rev` is split by fraction: `run` holds a half while the substream is unregistered
  (it sends `toPB` of it), and gives it to the goroutine with the `Created` on `recvc` (after
  which `run` reads it only once the goroutine is joined).
* `wcsPending s γ who r stopc donec cl`: `waitCancelSubstreams`' goroutines over `r.resuming` are
  running (`cl`: `stopc` closed); `wcsPending_close`, `wcsPending_join`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-- **`run`'s model of the stream's fields**: `substreams` (id ↦ substream), `resuming` (`null`: an
abandoned slot), `closeErr` (`none`: `nil`), and whether every substream goroutine has been joined
(`joinSubstreams`). -/
structure RunM where
  subs : List (Int × Loc)
  resuming : List Loc
  closeErr : Option CallErr
  joined : Bool

def RunM.init : RunM := { subs := [], resuming := [], closeErr := none, joined := true }

/-- **A substream's mutable fields**: its registered `id` (`-1`: none), `closing`, its position
(what it received: `initReq.rev` is `done + 1`), whether its `retc` is still pending (`nil` once
the channel was handed to `Watch`) and its `outc` still set. -/
structure WsM where
  id : Int
  closing : Bool
  pos : WatchPos
  retcPending : Bool
  outcSet : Bool

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

opaque wgsAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s w : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque wgsRun [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (who : Principal) (r : RunM) : IProp GF := iprop(True)
opaque wgsSend [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (who : Principal) (wc : GoInterface) : IProp GF := iprop(True)
opaque wgsRecv [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (who : Principal) (wc : GoInterface) : IProp GF := iprop(True)
/-- The right to close `s.donec` (once), held by `run` until its deferred teardown. -/
opaque wgsDoneTok [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque wsAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ws s : Loc) (γ : Cluster) (who : Principal) (w : WatchReq) : IProp GF := iprop(True)
opaque wsOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ws s : Loc) (γ : Cluster) (who : Principal) (q : WsM) : IProp GF := iprop(True)
opaque wsServe [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ws s : Loc) (γ : Cluster) (who : Principal) (resumec : Loc) : IProp GF := iprop(True)
opaque wsClosed [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ws s : Loc) (γ : Cluster) (who : Principal) (q : WsM) : IProp GF := iprop(True)
opaque wsCloser [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ws s : Loc) (γ : Cluster) (who : Principal) (m : WatchRespM) : IProp GF :=
  iprop(True)
opaque deliverOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (who : Principal) (tgt : Option Int) (m : WatchRespM) :
  IProp GF := iprop(True)
opaque wcsPending [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (who : Principal) (r : RunM) (stopc donec : Loc)
  (cl : Bool) : IProp GF := iprop(True)
/-- A `watchRequest` struct at `wr`: its read-only fields (all but `rev` and `retc`) are those of
the watch `w` over the context `ctx`. -/
opaque initReqAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (wr : Loc) (ctx : GoInterface) (w : WatchReq) : IProp GF := iprop(True)
/-- `waitCancelSubstreams`' stop channel: one `run` made for the call and alone closes. -/
opaque wcsStop [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s stopc : Loc) : IProp GF := iprop(True)
/-- `now` is `time.Now` (the buffer logger's clock; the only caller passes it). -/
opaque nowFuncOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (now : GoFunc) : IProp GF := iprop(True)
/-- The substream's buffer logger `bl` (`block_logger.go`'s `blockLogger`), whose callback
reads `ws`'s fields (run by `ws`'s goroutine, which owns them). Intended realization:
`blockLoggerAt bl A` with `A` the substream's fields its callback reads. -/
opaque bufLoggerAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (bl ws : Loc) : IProp GF := iprop(True)
/-- **A `*blockLogger`** (`block_logger.go`; persistent) whose `logFunc` keeps `A x` for every `x`:
its read-only fields (`interval`, `threshold`, `now`, `logFunc`) and its lock `mu` over the
counters. -/
opaque blockLoggerAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] {α : Type} (bl : Loc) (A : α → IProp GF) : IProp GF := iprop(True)

def watchInternal_persistent.spec : Prop :=
  (∀ s w γ who, Persistent (wgsAt (GF := GF) s w γ who)) ∧
  (∀ ws s γ who w, Persistent (wsAt (GF := GF) ws s γ who w)) ∧
  (∀ s γ who id m, Persistent (deliverOk (GF := GF) s γ who id m)) ∧
  (∀ wr ctx w, Persistent (initReqAt (GF := GF) wr ctx w)) ∧
  (∀ (α : Type) bl (A : α → IProp GF), Persistent (blockLoggerAt (GF := GF) bl A))

/-- **A `valCtx` is a context never done** (its `Done` the package's never-closed `valCtxCh`, its
`Err` `nil`, its values `inctx`'s): what `newWatcherGRPCStream` wraps `WithCancel` around. -/
def valCtx_ctxOk.spec : Prop := ∀ (vc : Loc) (inctx : GoInterface) (dflt p : Principal),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
    vc ↦□ ({ Context' := inctx } : go_etcd_io.etcd.client.v3.valCtx) ∗ Context.ctxOk inctx ∗
    ctxPrin dflt inctx p ⊢
  Context.ctxOk (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.valCtx.ty) #vc) ∗
  ctxPrin dflt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.valCtx.ty) #vc) p

/-- A response without events (a progress notification, broadcast to every substream) may be
shared: its header is read-only, it has no events. -/
def watchRespAt_noEvents_dup.spec : Prop := ∀ (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (m : WatchRespM), m.events = [] →
  watchRespAt (GF := GF) v m ⊢ watchRespAt v m ∗ watchRespAt v m

/-- `waitCancelSubstreams`' goroutines, once `stopc` is closed. -/
def wcsPending_close.spec : Prop := ∀ s γ who r (stopc donec : Loc),
  {{ wcsPending (GF := GF) s γ who r stopc donec false }}
    (App (App (Val (GoInstruction (FuncResolve go.close
      [(go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType []))]))) (Val #())) (Val #stopc))
  {{ RET #(); wcsPending s γ who r stopc donec true }}

/-- **Joining them** (`<-donec`): `run`'s state back, the substreams whose context was done meanwhile
marked closing (their `outc` closed and `nil`, each sent on `closingc` by a goroutine of `s.wg`). -/
def wcsPending_join.spec : Prop := ∀ s γ who r (stopc donec : Loc),
  {{ wcsPending (GF := GF) s γ who r stopc donec true }}
    (App (Val (chan.receive (go.GoType.StructType []))) (Val #donec))
  {{ (rv : val), RET rv; wgsRun s γ who r }}

end res

end ClientV3
end EtcdGrove
end Perennial
