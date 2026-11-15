/-
`(*watchableStore).NewWatchStream()`: a new watch stream of the store, without watchers.

**Users.** `watchServer.Watch` (`v3rpc/watch.go:179`, 2b: one stream per gRPC watch stream, through
the member's `WatchableKV`). Snippets: every `mvccwatch/` one.

**Proof sketch.** `watchStreamGauge.Inc()` (metrics: ambient, no panic); `make(chan WatchResponse,
chanBufLen)` (128: `watch_init.spec`); the maps. Allocates the stream's invariant (`wsAt`: the
channel's send protocol, the registrations' ghost map, the cancelled ids) and its tokens.

**Changes** from `specs-ref`'s file: the stream's state (`wsState`, client-owned under atomic updates)
replaced by persistent registration facts (`wsReg`, `wsCanceled`) and the control token `wsCtl`; the
consumer's `wsCons` kept (was `wsRecv`).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import SpecPlan.Spec.context.Api

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

/-- **`s.NewWatchStream()`**: a `*watchStream` of the store (as a `WatchStream`), named `ι`: its
control side (no id returned yet), its close right, its consumer (nothing received). -/
def watchableStore.NewWatchStream.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ watchableAt (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s) γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"NewWatchStream")) (Val #()))
  {{ (w : Loc), RET #(interface.mkOk (go.GoType.PointerType watchStream.ty) #w);
      ∃ ι : WsNames, wsAt w γ ι ∗ wsCtl ι 0 ∗ wsOpen ι ∗ wsCons ι [] }}

end spec

end Mvcc
end EtcdGrove
end Perennial
