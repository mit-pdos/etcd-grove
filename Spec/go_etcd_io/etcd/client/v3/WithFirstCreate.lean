/-
`clientv3.WithFirstCreate` (`client/v3/op.go`).

Users: `client/v3/concurrency` (`mutex.go`, `election.go`, `key.go`: `WithFirstCreate()`, `WithLastCreate()`), recipes (`queue.go` `WithFirstKey()`, `rwmutex.go` `WithLastRev()`), leasing (`WithLastRev()`).

Proof sketch: `withTop.spec`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/WithFirstCreate.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `WithFirstCreate()`: `WithPrefix(), WithSort(SortByCreateRevision, SortAscend), WithLimit(1)`. -/
def WithFirstCreate.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithFirstCreate)) (Val #()))
  {{ (sl : GoSlice), RET #sl; optsAt sl (withTopM SortByCreateRevision SortAscend) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
