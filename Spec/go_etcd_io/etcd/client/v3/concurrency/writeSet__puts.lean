/-
`(concurrency.writeSet).puts` (`client/v3/concurrency/stm.go`), internal.

Users: the STM's methods and commits (`stm.go`).

Proof sketch: a loop over the map, `append` of each entry's `op`.

Changes: from `specs-ref`'s `writeSet__puts.lean`: restated over `writeSetAt` and the `Attempt` model.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `ws.puts()`: the written keys' operations, in the map's order. -/
def writeSet.puts.spec : Prop :=
  ∀ (ws : GoMap) (writes : Key → Option WriteM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ writeSetAt ws writes }}
    (App (Val (ws @!! go_etcd_io.etcd.client.v3.concurrency.writeSet.ty @!! go!"puts")) (Val #()))
  {{ (sl : GoSlice), RET #sl; writeSetAt ws writes ∗ ∃ (ks : List GoString) (os : List OpM),
      ⌜keysOf writes ks ∧
        OpM.toReqOps os = some (ks.filterMap (fun k => (writes k).map (WriteM.op k)))⌝ ∗
      opsAt sl os }}

end spec

end Concurrency
end EtcdGrove
end Perennial
