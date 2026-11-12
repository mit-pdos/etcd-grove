/-
`NewStringAffineInterval(begin, end)`: the interval of two `StringAffineComparable`s.

**Users.** `watcherGroup.add/delete` (3f), `checkIntervals` (2a). **Proof sketch.** A struct literal.
**Changes.** Unchanged (over `strIvl`). **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.adt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

def NewStringAffineInterval.spec : Prop :=
  ∀ (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewStringAffineInterval)) (Val #b)) (Val #e))
  {{ RET #(strIvl b e); True }}

end spec

end Adt
end EtcdGrove
end Perennial
