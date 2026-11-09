/-
`(*watchStream).RequestProgress(id)`: a progress response for the watcher `id` if it is synced and
the store's revision is not below its start.

**Users.** `serverWatchStream.sendLoop` (`v3rpc/watch.go:594`, 2b: the ticker, for each watcher with
progress notification; may run after `Close`). Snippet: `mvccwatch/progress.go` `ReqProgressOne`.

**Proof sketch.** Under `ws.mu` the watcher; `watchable.progress` (`progressIfSync` with `id`, a reader
token for `s.mu`'s reader slot): the response, if sent, carries `progStep` at the store's
revision (the stream's invariant). After `Close` no watcher is synced: nothing is sent.

**Changes** from `specs-ref`'s file: a reader token of 3e's `mvccReaders` (one per call, given back). **Margin.** What it
sends is the channel's business (`wsRespOk`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import Spec.context.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watchStream.RequestProgress.spec : Prop :=
  ∀ (w : Loc) (γ : MvccName) (ι : WsNames) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsAt w γ ι ∗ mvccReaders γ 1 }}
    (App (Val (w @!! go.GoType.PointerType watchStream.ty @!! go!"RequestProgress")) (Val #id))
  {{ RET #(); mvccReaders γ 1 }}

end spec

end Mvcc
end EtcdGrove
end Perennial
