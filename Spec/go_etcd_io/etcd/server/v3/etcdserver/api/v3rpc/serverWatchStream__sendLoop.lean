/-
`v3rpc.serverWatchStream.sendLoop` (`watch.go`). Lean-first (no Rocq counterpart); the
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

/-- **`sws.sendLoop()`**: sends down the mvcc watch stream's responses (buffered until their
watch id's created response is sent), the control responses (a created one after draining the
stream's channel down to its watcher's stamp) and, on the progress ticker, asks for the progress of
the watchers that want it; until a send fails, the control stream or the mvcc stream's channel is
closed, or `closec` is. Every response it sends at down position `j` carries `watchDn j m`
(`watchStreamSpec`). The mvcc API migration (2026-11-05, the draft
`notes/mvcc-api-clients/WatchSpecs.lean` §6): the consumer's `wsRecv ι []` and the received list's
authority at `[]` in place of mvcc's `watchConsumer`; the thread bound stays, for
`GetProgressReportInterval`; (the store's readers as client-held tokens, 2026-11-07) a reader token
of the store (`mvccReaders r.W.γm 1`, which `RequestProgress` takes; `lean`'s store reader slot). -/
abbrev v3rpc.serverWatchStream.sendLoop.spec : Prop :=
  ∀ (sws : Loc) (r : v3rpc.WRun GF) (Up : Nat → v3rpc.WatchReqM → IProp GF)
    (Dn : Nat → v3rpc.WatchRespM → IProp GF) (st : GoInterface) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.swsIs sws r Up Dn st ci cd ∗ v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) r.γs [] ∗
      spscConsumer r.γctrl ([] : List Loc) ∗ mvcc.api.wsRecv r.ι [] ∗
      monoListAuthOwn r.γr 1 ([] : List mvcc.api.WResp) ∗
      ⌜threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders ∧ 5 ≤ threadBound GF⌝ ∗
      sync.ownRWMutex (v3rpc.swsF sws go!"mu") (v3rpc.swsMu r.pm r.vm r.fm) ∗ threadTok ∗
      mvcc.api.mvccReaders r.W.γm 1 }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"sendLoop")) (Val #()))
  {{ RET #(); threadTok ∗ mvcc.api.mvccReaders r.W.γm 1 }}

end spec

end EtcdGrove
end Perennial
