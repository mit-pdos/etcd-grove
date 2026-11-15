/-
`(concurrency.writeSet).cmps` (`client/v3/concurrency/stm.go`), internal.

Users: the STM's methods and commits (`stm.go`).

Proof sketch: a loop over the map: `ModRevision.spec`, `Compare.spec`, `append`.

Changes: from `specs-ref`'s `writeSet__cmps.lean`: restated over `writeSetAt` and the `Attempt` model.

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

/-- `ws.cmps(rev)`: `ModRevision(k) < rev` per written key, in the map's order. -/
def writeSet.cmps.spec : Prop :=
  ∀ (ws : GoMap) (writes : Key → Option WriteM) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ writeSetAt ws writes }}
    (App (Val (ws @!! go_etcd_io.etcd.client.v3.concurrency.writeSet.ty @!! go!"cmps")) (Val #rev))
  {{ (sl : GoSlice), RET #sl; writeSetAt ws writes ∗ ∃ ks : List GoString, ⌜keysOf writes ks⌝ ∗
      cmpsAt sl (ks.map (fun k => some (writeCmp rev k))) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
