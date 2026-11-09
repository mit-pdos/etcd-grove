/-
`(*serverWatchStream).close()` (`watch.go`): ends a run.

**Users.** `watchServer.Watch` (`watch.go:235`), once.

**Proof sketch.** `swsCloser`: mvcc's `Close()` (3f: every watcher canceled, the channel closed,
once; later calls of the receive loop's `Watch`, `Cancel`, `RequestProgress*` on the closed stream
refuse or do nothing, never sending on the closed channel), `close(sws.closec)` (the closer's,
once), `sws.wg.Wait()` (the send loop's goroutine has returned: its `Done`).

**Changes** from `specs-ref`'s file: the run record, the close token, the broadcast channel's
pending state and the wait group's adder replaced by the run's shares (`swsAt`, `swsCloser`).

**Margin.** Gives nothing back (the handler returns next).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchInternal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`sws.close()`**: closes the run's mvcc stream and `closec`, and waits for the send loop. -/
def serverWatchStream.close.spec : Prop :=
  ∀ (sws : Loc) (γ : Cluster) (who : Principal) (st : GoInterface) (g : WatchStreamNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      swsAt sws γ who st g ∗ swsCloser sws }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"close")) (Val #()))
  {{ RET #(); True }}

end spec

end V3rpc
end EtcdGrove
end Perennial
