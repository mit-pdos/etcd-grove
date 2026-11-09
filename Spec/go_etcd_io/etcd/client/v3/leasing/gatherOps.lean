/-
`gatherOps` (`util.go`): the operations with each transaction replaced by its branches' (appending
a nested transaction's `elseOps` into its `thenOps`, beyond its length: the caller's memory). Stated
for operations that are not transactions (all the leasing KV passes: `flatTxn`), where it copies
them. Changes: the old spec covered trees with owned capacities (`opTAtC`); flat only now.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `gatherOps(ops)` of operations that are not transactions: a copy. -/
def gatherOps.spec : Prop :=
  ∀ (ops : GoSlice) (os : List OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ opsAt ops os ∗ ⌜∀ o ∈ os, o.t ≠ tTxn⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.gatherOps)) (Val #ops))
  {{ (ret : GoSlice), RET #ret; opsAt ops os ∗ opsAt ret os }}

end spec

end Leasing
end EtcdGrove
end Perennial
