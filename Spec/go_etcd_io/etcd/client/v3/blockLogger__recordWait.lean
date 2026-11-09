/-
`(*clientv3.blockLogger).recordWait(d)` (`client/v3/block_logger.go`).

**Users**: `watchGRPCStream.recordBufWait` (`client/v3/watch.go`, the substream's goroutine, which
owns the fields its callback reads). **Proof sketch**: lock `mu` (`blockLoggerAt`'s lock
invariant: the counters), add to them, call `now()`; if the window passed and the threshold is
exceeded, call `logFunc` with `A x` (its triple); reset; unlock. **Changes** from
`specs-ref/Spec/go_etcd_io/etcd/client/v3/blockLogger__recordWait.lean`: unchanged (over the opaque
`blockLoggerAt`); added at integration (I1). **Margin**: the counters are not modelled.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WatchInternal

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

/-- `l.recordWait(d)` keeps the logger's `A x` (its `logFunc`'s). -/
def blockLogger.recordWait.spec : Prop :=
  ∀ (α : Type) (A : α → IProp GF) (x : α) (bl : Loc) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ blockLoggerAt bl A ∗ A x }}
    (App (Val (bl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.blockLogger.ty @!! go!"recordWait"))
      (Val #d))
  {{ RET #(); A x }}

end spec

end ClientV3
end EtcdGrove
end Perennial
