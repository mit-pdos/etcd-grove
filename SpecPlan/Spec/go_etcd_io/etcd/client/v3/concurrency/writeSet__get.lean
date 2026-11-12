/-
`(concurrency.writeSet).get` (`client/v3/concurrency/stm.go`), internal.

Users: the STM's methods and commits (`stm.go`).

Proof sketch: a loop over the keys, the map's lookup, a fresh copy.

Changes: from `specs-ref`'s `writeSet__get.lean`: restated over `writeSetAt` and the `Attempt` model.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.concurrency.Api

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

/-- `ws.get(keys...)`: a copy of the first written key's entry, or `nil`. -/
def writeSet.get.spec : Prop :=
  ∀ (ws : GoMap) (writes : Key → Option WriteM) (sl : GoSlice) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ writeSetAt ws writes ∗ sl ↦*□ ks }}
    (App (Val (ws @!! go_etcd_io.etcd.client.v3.concurrency.writeSet.ty @!! go!"get")) (Val #sl))
  {{ (p : Loc), RET #p; writeSetAt ws writes ∗
      ((⌜p = null ∧ ks.find? (fun k => decide (writes k ≠ none)) = none⌝) ∨
       (∃ (k : GoString) (w : WriteM) (sp : go_etcd_io.etcd.client.v3.concurrency.stmPut),
          ⌜ks.find? (fun k => decide (writes k ≠ none)) = some k ∧ writes k = some w ∧
            sp.val' = w.value⌝ ∗ p ↦ sp)) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
