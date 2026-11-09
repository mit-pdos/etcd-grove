/-
`clientv3.NewWatcher(c)` (`client/v3/watch.go`).

**Users**: `newClient` (`E client/v3/client.go:460`, 1c: the `Watcher` field of `New`'s client,
`isClient_fields`'s `watcherAt`). **Proof sketch**: `pb.NewWatchClient(c.conn)` (3h's stub over
`connOk`: `remoteWatchAt`, `req/go_etcd_io_etcd_api_v3_etcdserverpb.md`), then
`NewWatchFromWatchClient.spec` (`clientBase`: `clientCore_pre`, `clientPre_base`). **Changes**
from `specs-ref/.../NewWatcher.lean`: over 1c's `clientCore` (was the old environment `WEnv`; at
integration `clientCore`, as 1c's sibling constructors `NewLease`, `NewAuth` take: it gives W0's
`clientConnOk` by `clientConnOk_core` for the stub over `c.conn`, and `clientBase` for
`NewWatchFromWatchClient`). **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiWatch
public import Spec.go_etcd_io.etcd.client.v3.ApiClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewWatcher(c)`: a watcher of the client's cluster as its principal. -/
def NewWatcher.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewWatcher)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ w : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty) #w⌝ ∗
      watcherHandle w γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
