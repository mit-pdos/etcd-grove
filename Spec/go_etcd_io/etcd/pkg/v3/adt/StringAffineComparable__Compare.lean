/-
`StringAffineComparable.Compare(c)`: the affine order (`""` the top); `c` must be a
`StringAffineComparable` (else the type assertion panics: a tree never mixes kinds).

**Users.** The tree's searches (`Insert`, `find`, `visit`, `Intersects`, `Contains`, `updateMax`),
through `Interval.Compare`. **Proof sketch.** The length tests and Go's string order. **Changes.**
Unchanged. **Margin.** None.
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

def StringAffineComparable.Compare.spec : Prop :=
  ∀ (s s' : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt }}
    (App (Val (s @!! StringAffineComparable.ty @!! go!"Compare"))
      (Val #(interface.mkOk StringAffineComparable.ty #s')))
  {{ RET #(W64 (affCmp s s')); True }}

end spec

end Adt
end EtcdGrove
end Perennial
