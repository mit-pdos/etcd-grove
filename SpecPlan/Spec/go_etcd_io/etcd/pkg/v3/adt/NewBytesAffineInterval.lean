/-
`NewBytesAffineInterval(begin, end)`: the interval of two `BytesAffineComparable`s (the slices
themselves, not copied).

**Users.** `getMergedPerms`, `checkKeyInterval` (`auth/range_perm_cache.go`, 3d). **Proof sketch.** A
struct literal. **Changes.** Unchanged (over `Cmp.bytes.ivl`). **Margin.** None.
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

def NewBytesAffineInterval.spec : Prop :=
  ∀ (b e : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewBytesAffineInterval)) (Val #b)) (Val #e))
  {{ RET #(Cmp.bytes.ivl #b #e); True }}

end spec

end Adt
end EtcdGrove
end Perennial
