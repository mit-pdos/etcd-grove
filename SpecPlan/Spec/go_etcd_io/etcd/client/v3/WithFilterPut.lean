/-
`clientv3.WithFilterPut` (`client/v3/op.go`).

Users: the users' `Get`/`Delete`/`Put`/`Watch` calls (see `kv.Get`, `kv.Put`): `WithPrefix`
(concurrency, recipes, the cache, Kubernetes), `WithRev` (concurrency, recipes, the cache,
Kubernetes' reads and watches), `WithLimit`, `WithRange`, `WithKeysOnly`, `WithCountOnly`
(Kubernetes, the cache), `WithLease` (concurrency's `Session` keys, leasing), `WithSerializable`
(concurrency's `stmSerializable`), the revision filters (concurrency's `waitDeletes`, recipes), the
watch options (1b's users). Snippet: `clientv3kv/ops.go` (`ReqGetOptions`).

Proof sketch: a closure over its arguments (read-only cells), which sets the put filter: `optAt`.

Changes: none (no old spec): added for the users named above.

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

/-- `WithFilterPut(...)`: an option that sets the put filter. -/
def WithFilterPut.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithFilterPut)) (Val #()))
  {{ (f : GoFunc), RET #f; optAt f (withFilterPutM) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
