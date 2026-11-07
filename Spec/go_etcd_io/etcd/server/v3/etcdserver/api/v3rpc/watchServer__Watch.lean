/-
`v3rpc.watchServer.Watch` (`watch.go`): the watch slice's server hop. Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`ws.Watch(stream)`**: a run on a fresh server end of a stream (`srvStreamIs` with both
tokens at the empty queues), whose content of the responses sent down is the watch server's
(`watchStreamSpec`: the handler's `Dn` is `watchDn`, at the server's side of the watch path `W`),
the client's content of its requests restricted with (G2's freeze) the client's bound per create
request (`upOk`), the stream's auxiliary name (set to the run's ghost names, `auxOf`; the watch
slice's unit W-C) and the run's resources (the auth store's reader resource and the thread bound):
it returns, with the stream specification. The specification is at the token of the run's context
`ci` (`auth.ctxTokenOf`; G2, 2026-10-30): each create's check passed for it (`watchAuthed`). The
mvcc API migration (2026-11-05, the draft `notes/mvcc-api-clients/WatchSpecs.lean` §6): the
server's side of the watch path (`srvWOk`, with v3rpc's namespace); no watch token per create and no
reader slots (`watchRunSlot` was `recvRes ∗ sendRes`, the store's reader slots: now `R.E.RD ∗
⌜threadBound …⌝`); the handler's thread token (the API's `Close` takes one); the run's names and
its invariant `wsInv` allocated from `NewWatchStream`'s `wsState ι wsStart ∗ wsRecv ι []`; (the
store's readers as client-held tokens, 2026-11-07) two reader tokens of the store
(`mvccReaders W.γm 2`), one for each loop (`lean`'s two store reader slots, `recvRes`/`sendRes`),
not given back (the receive loop is not joined). -/
abbrev v3rpc.watchServer.Watch.spec : Prop :=
  ∀ (p : Loc) (R : v3rpc.WSrv GF) (W : v3rpc.SrvW GF) (st : GoInterface) (γs : v3rpc.StreamNames)
    (Up : Nat → v3rpc.WatchReqM → IProp GF) (Dn : Nat → v3rpc.WatchRespM → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.isWatchServer p R ∗ v3rpc.srvWOk W R.wsl v3rpc.wsN ∗
      v3rpc.srvStreamIs st γs v3rpc.pbWatchRequest v3rpc.pbWatchResponse Up Dn ci cd ∗
      v3rpc.watchStreamSpec γs R W (auth.ctxTokenOf (GoInterface.ok ci)) Dn ∗
      v3rpc.upOk R.E.authMode Up ∗
      v3rpc.srvRecvTok (Req := v3rpc.pbWatchRequest) γs [] ∗
      v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) γs [] ∗
      v3rpc.streamAuxTok γs ∗ R.E.RD ∗ ⌜threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders⌝ ∗
      threadTok ∗ mvcc.api.mvccReaders W.γm 2 }}
    (App (Val (p @!! go.GoType.PointerType v3rpc.watchServer.ty @!! go!"Watch")) (Val #st))
  {{ (err : GoInterface), RET #err; threadTok ∗
      v3rpc.watchStreamSpec γs R W (auth.ctxTokenOf (GoInterface.ok ci)) Dn }}

end spec

end EtcdGrove
end Perennial
