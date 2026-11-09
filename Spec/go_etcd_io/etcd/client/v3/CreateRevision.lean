/-
`clientv3.CreateRevision` (`client/v3/compare.go`).

Users: `client/v3/concurrency` (`mutex.go`, `election.go`: `Compare(CreateRevision(k), "=", 0)`;
`stm.go`: `Compare(ModRevision(k), "<", rev+1)`, `Compare(Value(k), "=", v)`), recipes
(`key.go`, `client.go`: `ModRevision`, `Version`), leasing (`txn.go`, `kv.go`: `CreateRevision`,
`ModRevision`, `LeaseValue`), Kubernetes' store (`Compare(ModRevision(key), "=", rv)`) and
compactor (`Compare(Version(key), "=", t)`), the examples (`txnlin/linkvtxn.go:804` `cmpOf`).
Snippet: `clientv3kv/txn.go`.

Proof sketch: a fresh `Compare` message (persisted).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/CreateRevision.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `CreateRevision(key)`: a comparison of the key's create, nothing else set. -/
def CreateRevision.spec : Prop :=
  ∀ (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.CreateRevision)) (Val #key))
  {{ (c : go_etcd_io.etcd.client.v3.Cmp), RET #c; cmpAt c (some (cmpOfTarget cmpTCreate key)) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
