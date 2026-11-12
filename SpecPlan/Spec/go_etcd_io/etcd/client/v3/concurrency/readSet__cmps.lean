/-
`(concurrency.readSet).cmps` (`client/v3/concurrency/stm.go`), internal.

Users: the STM's methods and commits (`stm.go`).

Proof sketch: a loop over the map: `isKeyCurrent.spec`, `append`.

Changes: from `specs-ref`'s `readSet__cmps.lean`: restated over `readSetAt` and the `Attempt` model.

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

/-- `rs.cmps()`: one `isKeyCurrent` comparison per read, in the map's order. -/
def readSet.cmps.spec : Prop :=
  ∀ (rs : GoMap) (γ : Cluster) (reads : Key → Option ReadM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ readSetAt rs γ reads }}
    (App (Val (rs @!! go_etcd_io.etcd.client.v3.concurrency.readSet.ty @!! go!"cmps")) (Val #()))
  {{ (sl : GoSlice), RET #sl; readSetAt rs γ reads ∗ ∃ ks : List GoString, ⌜keysOf reads ks⌝ ∗
      cmpsAt sl (ks.filterMap (fun k => (reads k).map (fun e => some (curCmp k e)))) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
