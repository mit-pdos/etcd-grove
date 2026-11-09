/-
`clientv3.WithRev` (`client/v3/op.go`).

Users: the users' `Get`/`Delete`/`Put`/`Watch` calls (see `kv.Get`, `kv.Put`): `WithPrefix`
(concurrency, recipes, the cache, Kubernetes), `WithRev` (concurrency, recipes, the cache,
Kubernetes' reads and watches), `WithLimit`, `WithRange`, `WithKeysOnly`, `WithCountOnly`
(Kubernetes, the cache), `WithLease` (concurrency's `Session` keys, leasing), `WithSerializable`
(concurrency's `stmSerializable`), the revision filters (concurrency's `waitDeletes`, recipes), the
watch options (1b's users). Snippet: `clientv3kv/ops.go` (`ReqGetOptions`).

Proof sketch: a closure over its arguments (read-only cells), which sets the revision: `optAt`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/WithRev.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `WithRev(...)`: an option that sets the revision. -/
def WithRev.spec : Prop :=
  ∀ (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithRev)) (Val #rev))
  {{ (f : GoFunc), RET #f; optAt f (withRevM rev) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
