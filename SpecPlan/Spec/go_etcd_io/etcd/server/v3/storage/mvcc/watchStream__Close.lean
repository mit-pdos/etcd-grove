/-
`(*watchStream).Close()`: cancels every watcher and closes the channel.

**Users.** `serverWatchStream.close` (`v3rpc/watch.go:668`, 2b, once per run). Snippet:
`mvccwatch/lifecycle.go` `ReqClose`.

**Proof sketch.** Under `ws.mu`: each cancel closure (as `Cancel`'s: after it no response of the
watcher is sent; a watcher a concurrent `Cancel` already removed is found with `ch` `nil`); `closed`
set; `close(ws.ch)` (no send can follow: every watcher of the stream is out of the store's groups
and victims, and `RequestProgress*` find no synced watcher: `progressIfSync` sends nothing); the
gauge. The open token is spent (a second `close` panics).

**Changes** from `specs-ref`'s file: the atomic update over the stream's state replaced by the open
token and the persistent `wsClosed`.

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

def watchStream.Close.spec : Prop :=
  ∀ (w : Loc) (γ : MvccName) (ι : WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsAt w γ ι ∗ wsOpen ι }}
    (App (Val (w @!! go.GoType.PointerType watchStream.ty @!! go!"Close")) (Val #()))
  {{ RET #(); wsClosed ι }}

end spec

end Mvcc
end EtcdGrove
end Perennial
