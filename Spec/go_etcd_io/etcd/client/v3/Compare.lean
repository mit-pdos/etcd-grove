/-
`clientv3.Compare` (`client/v3/compare.go`).

Users: `client/v3/concurrency` (`mutex.go`, `election.go`: `Compare(CreateRevision(k), "=", 0)`;
`stm.go`: `Compare(ModRevision(k), "<", rev+1)`, `Compare(Value(k), "=", v)`), recipes
(`key.go`, `client.go`: `ModRevision`, `Version`), leasing (`txn.go`, `kv.go`: `CreateRevision`,
`ModRevision`, `LeaseValue`), Kubernetes' store (`Compare(ModRevision(key), "=", rv)`) and
compactor (`Compare(Version(key), "=", t)`), the examples (`txnlin/linkvtxn.go:804` `cmpOf`).
Snippet: `clientv3kv/txn.go`.

Proof sketch: `Cmp.Clone.spec`, `Cmp.ensureCompare.spec`, the result's string compared; by the target, `mustInt64.spec`/`mustInt64orLeaseID.spec` or the type assertion to `string`; the fields written in the fresh copy (persisted).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Compare.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

verify-round: the fresh `*pb.Compare` (its `protoRest` from `protoRest_zero` at `own 1`) is made read-only for `cmpAt` by `protoRest_persist` (A1-provability F6: the sketch had no law for it).

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

/-- `Compare(cmp, result, v)`: the comparison with its result operator and value set (premise:
a known result and a value of the target's type, else it panics). -/
def Compare.spec : Prop :=
  ∀ (c : go_etcd_io.etcd.client.v3.Cmp) (m : Option EtcdModel.Compare) (result : GoString) (a : CmpArg)
    (m' : EtcdModel.Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpAt c m ∗ ⌜compareM m result a = some m'⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.Compare)) (Val #c)) (Val #result)) (Val #(a.toIface)))
  {{ (c' : go_etcd_io.etcd.client.v3.Cmp), RET #c'; cmpAt c' (some m') }}

end spec

end ClientV3
end EtcdGrove
end Perennial
