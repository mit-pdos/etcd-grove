/-
`clientv3.newBlockLogger(interval, threshold, now, logFunc)` (`client/v3/block_logger.go`).

**Users**: `watchGRPCStream.newWatcherStreamBufLogger` (`client/v3/watch.go`, with `time.Now` and a
callback logging the substream's fields). **Proof sketch**: `now` defaults to `time.Now` when `nil`
(Perennial's `time.Now` spec); allocate the struct, call `now()` once for `lastLogTime`; make the
lock invariant over the counters (`blockLoggerAt`). **Changes** from
`specs-ref/Spec/go_etcd_io/etcd/client/v3/newBlockLogger.lean`: unchanged (over the opaque
`blockLoggerAt`, was `isBlockLogger`); added at integration (I1): neither 1b nor 1c had specified
`block_logger.go`. **Margin**: no claim about when the callback runs.
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

/-- `newBlockLogger(interval, threshold, now, logFunc)`, with `now` `nil` or returning a time and a
`logFunc` that keeps `A x` for every `x`: a block logger. -/
def newBlockLogger.spec : Prop :=
  ∀ (α : Type) (A : α → IProp GF) (iv th : _root_.Perennial.time.Duration) (nowf lf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      (⌜nowf = func.nil⌝ ∨ □ ∀ Φ : val → IProp GF, ▷ (∀ t : _root_.Perennial.time.Time, Φ #t) -∗
        WP (App (Val #nowf) (Val #())) {{ Φ }}) ∗
      (□ ∀ (x : α) (n : w64) (d1 d2 : _root_.Perennial.time.Duration),
        {{ A x }} (App (App (App (Val #lf) (Val #n)) (Val #d1)) (Val #d2)) {{ RET #(); A x }}) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.newBlockLogger)) (Val #iv)) (Val #th))
      (Val #nowf)) (Val #lf))
  {{ (bl : Loc), RET #bl; blockLoggerAt bl A }}

end spec

end ClientV3
end EtcdGrove
end Perennial
