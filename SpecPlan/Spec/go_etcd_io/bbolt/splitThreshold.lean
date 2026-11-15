/-
`splitThreshold(pageSize, fillPercent)` (`node.go`, the fork's trusted helper, D17): `int(pageSize * clamp(fillPercent))`; its model bounds it.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) at most the page size unless `fillPercent` is a NaN. -/
def splitThreshold.spec : Prop :=
  ∀ [HasExt osFsExt] (ps f : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ⌜¬ float64IsNaN f ∧ uint.nat ps < 2 ^ 53⌝ }}
    (App (App (Val (@! go_etcd_io.bbolt.splitThreshold)) (Val #ps)) (Val #f))
  {{ (t : w64), RET #t; ⌜0 ≤ sint.Z t ∧ sint.Z t ≤ uint.nat ps⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
