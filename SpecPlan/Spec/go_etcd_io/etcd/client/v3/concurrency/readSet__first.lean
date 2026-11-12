/-
`(concurrency.readSet).first` (`client/v3/concurrency/stm.go`), internal.

Users: the STM's methods and commits (`stm.go`).

Proof sketch: a loop over the map.

Changes: from `specs-ref`'s `readSet__first.lean`: restated over `readSetAt` and the `Attempt` model.

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

/-- `rs.first()`: the least header revision of the reads, `MaxInt64 - 1` if none is less. -/
def readSet.first.spec : Prop :=
  ∀ (rs : GoMap) (γ : Cluster) (reads : Key → Option ReadM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ readSetAt rs γ reads }}
    (App (Val (rs @!! go_etcd_io.etcd.client.v3.concurrency.readSet.ty @!! go!"first")) (Val #()))
  {{ (f : w64), RET #f; readSetAt rs γ reads ∗
      ⌜sint.Z f ≤ 2 ^ 63 - 2 ∧ (∀ k e, reads k = some e → sint.Z f ≤ e.hdr) ∧
        (sint.Z f = 2 ^ 63 - 2 ∨ ∃ k e, reads k = some e ∧ sint.Z f = e.hdr)⌝ }}

end spec

end Concurrency
end EtcdGrove
end Perennial
