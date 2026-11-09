/-
`NewStringAffinePoint(s)`: the point interval `[s, s + "\x00")`.

**Users.** `watcherGroup.contains/watcherSetByKey` (3f), `checkIntervals` (2a). **Proof sketch.**
`NewStringAffineInterval`. **Changes.** Unchanged. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Api

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

def NewStringAffinePoint.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewStringAffinePoint)) (Val #s))
  {{ RET #(strIvl (pointOf s).1 (pointOf s).2); True }}

end spec

end Adt
end EtcdGrove
end Perennial
