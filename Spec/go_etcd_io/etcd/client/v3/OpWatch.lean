/-
`clientv3.OpWatch` (`client/v3/op.go`).

Users: `watcher.Watch` (1b), the cache (`cache/cache.go` `validateWatch`).

Proof sketch: `Op{t, key}` then `Op.applyOpts.spec`, the `switch` (premise).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/OpWatch.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `OpWatch(key, opts...)`: a watch's `Op` over `key` with the options applied. -/
def OpWatch.spec : Prop :=
  ∀ (key : GoString) (sl : GoSlice) (gs : List (OpM → OpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAt sl gs ∗ ⌜¬ (opWatchM key gs).watchPanics⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.OpWatch)) (Val #key)) (Val #sl))
  {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; optsAt sl gs ∗ opAt op (opWatchM key gs) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
