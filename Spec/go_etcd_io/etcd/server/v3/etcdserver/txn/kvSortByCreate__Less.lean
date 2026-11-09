/-
`(*kvSortByCreate).Less(i, j)` (`range.go`), internal (`sort.Sort`'s comparator): mirrors the code: the strict
order of create revisions (`(a - b) < 0`), W0's `targetLt targetCreate` (a difference of two numbers in `[0, 2 ^ 63)` does not
overflow: `kvFits`). Old spec: `kvLtBy`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

open Classical in
/-- `s.Less(i, j)`: `targetLt targetCreate` of the `i`-th and `j`-th key-values. -/
def kvSortByCreate.Less.spec : Prop :=
  ∀ (sp ks : Loc) (sl : GoSlice) (dq dq' : DFrac) (ps : List Loc) (kvs : List KV) (i j : w64)
    (a b : KV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ sp.[go_etcd_io.etcd.server.v3.etcdserver.txn.kvSortByCreate, go!"kvSort"] ↦□ ks ∗ ks.[go_etcd_io.etcd.server.v3.etcdserver.txn.kvSort, go!"kvs"] ↦□ sl ∗
      sl ↦*{dq} ps ∗ ([∗list] p; kv ∈ ps; kvs, keyValueOwn p dq' (KeyValueM.ofKV kv)) ∗
      ⌜(∀ kv ∈ kvs, kvFits kv) ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧
        kvs[sint.nat i]? = some a ∧ kvs[sint.nat j]? = some b⌝ }}
    (App (App (Val (sp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.txn.kvSortByCreate.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ RET #(decide (targetLt targetCreate a b)); sl ↦*{dq} ps ∗
      ([∗list] p; kv ∈ ps; kvs, keyValueOwn p dq' (KeyValueM.ofKV kv)) }}

end spec
end Txn
end EtcdGrove
end Perennial
