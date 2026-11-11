/-
`v3rpc.serverWatchStream.recvLoop` (`watch.go`). Lean-first (no Rocq counterpart); the
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

/-- **`sws.recvLoop()`**: receives the client's requests until the stream ends (`io.EOF`: `nil`;
another error: it), or `closec` is closed (`nil`): each create request is registered with the
mvcc watch stream (`Watch`, its update `WatchApi.watch_au`, the registry entry and the id token
minted at its commit) or refused, each cancel request cancels (`Cancel`, the client's cancel
request kept in the run's invariant), each progress request asks for the progress of all; every
create and cancel request answered by a control response on the control stream (`ctrlP`: the
response answers the request at its position, with the answer token it mints from `ansPool` when it
receives the request; the watch slice's unit W-C). The mvcc API migration (2026-11-05, the draft
`notes/mvcc-api-clients/WatchSpecs.lean` §6): the thread token in place of the store's reader slot
(the API's `Watch`, `Cancel`, `Rev` and `RequestProgressAll` take one), and (the store's readers as
client-held tokens, 2026-11-07) a reader token of the store (`mvccReaders r.W.γm 1`: `Watch`, `Rev`
and `RequestProgressAll` take one, as `lean`'s store reader slot); the auth store's reader resource
`r.srv.E.RD` (`isWatchPermitted`).
Returns the control stream's producer token, and an error that is `nil` or the stream's
(`streamErr`: `Recv`'s error, with the error tree `Watch`'s `errors.Is(err, context.Canceled)`
needs; premise-fixes-6, 2026-11-11, in place of only a typed error). -/
abbrev v3rpc.serverWatchStream.recvLoop.spec : Prop :=
  ∀ (sws : Loc) (r : v3rpc.WRun GF) (Up : Nat → v3rpc.WatchReqM → IProp GF)
    (Dn : Nat → v3rpc.WatchRespM → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (L : List v3rpc.WatchReqM) (sent : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.swsIs sws r Up Dn st ci cd ∗ v3rpc.srvRecvTok (Req := v3rpc.pbWatchRequest) r.γs L ∗
      spscProducer r.γctrl sent ∗ v3rpc.ansPool r.γa L.length ∗ r.srv.E.RD ∗ threadTok ∗
      mvcc.api.mvccReaders r.W.γm 1 }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"recvLoop")) (Val #()))
  {{ (err : GoInterface), RET #err; (⌜err = GoInterface.nil⌝ ∨ v3rpc.streamErr err) ∗
      threadTok ∗ mvcc.api.mvccReaders r.W.γm 1 ∗ ∃ sent' : List Loc, spscProducer r.γctrl sent' }}

end spec

end EtcdGrove
end Perennial
