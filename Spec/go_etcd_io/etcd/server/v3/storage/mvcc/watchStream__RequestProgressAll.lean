/-
`(*watchStream).RequestProgressAll()`: a progress response of id `-1` at the store's revision, if
every watcher of the stream is synced (and the revision not below any start); `true` then (or when
there is no watcher).

**Users.** `serverWatchStream.recvLoop` (`v3rpc/watch.go:400`, 2b: a progress request, under
`sws.mu`). Snippet: `mvccwatch/progress.go` `ReqProgressAll`.

**Proof sketch.** Under `ws.mu` (registrations and cancellations excluded), `progressAll` over the
stream's watchers (`progressIfSync` with `-1`, the reader token): the response covers exactly the
watchers live then (registered, by stamp, and not removed by a cancel), each synced: `progStep`.

**Changes** from `specs-ref`'s file: a reader token of 3e's `mvccReaders` (one per call, given back). **Margin.** The
result is not stated (no caller reads it).
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

def watchStream.RequestProgressAll.spec : Prop :=
  ∀ (w : Loc) (γ : MvccName) (ι : WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsAt w γ ι ∗ mvccReaders γ 1 }}
    (App (Val (w @!! go.GoType.PointerType watchStream.ty @!! go!"RequestProgressAll")) (Val #()))
  {{ (b : Bool), RET #b; mvccReaders γ 1 }}

end spec

end Mvcc
end EtcdGrove
end Perennial
