/-
`clientv3.WithLastKey` (`client/v3/op.go`).

Users: `client/v3/concurrency` (`mutex.go`, `election.go`, `key.go`: `WithFirstCreate()`, `WithLastCreate()`), recipes (`queue.go` `WithFirstKey()`, `rwmutex.go` `WithLastRev()`), leasing (`WithLastRev()`).

Proof sketch: `withTop.spec`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/WithLastKey.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `WithLastKey()`: `WithPrefix(), WithSort(SortByKey, SortDescend), WithLimit(1)`. -/
def WithLastKey.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithLastKey)) (Val #()))
  {{ (sl : GoSlice), RET #sl; optsAt sl (withTopM SortByKey SortDescend) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
