/-
`(*clientv3.watcher).Close()` (`client/v3/watch.go`).

**Users**: `Client.Close` (`E client/v3/client.go:150`, the error dropped), the namespace wrapper
(`namespace/watch.go:79`). Snippet `clientv3watch/ending.go` `ReqWatcherClose`.

**Proof sketch.** Under `mu`, take the map and set `streams` to `nil` (the lock invariant's closed
state: later `Watch`es return a closed channel); for each stream, `watchGRPCStream.close.spec`
(persistent `wgsAt`: concurrent closes are fine); `errors.Is` (2a's spec, any error).

**Changes**: over `watcherHandle`. verify-round (W3): the handle records its client `c`; no
`clientReady c` (`Close` opens no stream). **Margin**: the error is not modelled; that every watch's
channel then closes is liveness. `issues/etcd-watch-close-hang-refused-create.md` (a hang, fixed
or not, is liveness only).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiWatch

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

/-- `watcher.Close` meets `Watcher.CloseTriple`. -/
def watcher.Close.spec : Prop :=
  ∀ (w c : Loc) (γ : Cluster) (who : Principal),
  Watcher.CloseTriple (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"Close")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ watcherHandle w c γ who))

end spec

end ClientV3
end EtcdGrove
end Perennial
