/-
`BytesAffineComparable.Compare(c)`: the affine order of the slices' contents (`bytes.Compare`, the
empty slice the top); `c` a `BytesAffineComparable`.

**Users.** As `StringAffineComparable.Compare`, for the auth store's trees. **Proof sketch.** The
length tests, Perennial's `bytes.Compare`. **Changes.** Unchanged. **Margin.** None.
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

def BytesAffineComparable.Compare.spec : Prop :=
  ∀ (s s' : GoSlice) (bs bs' : GoString) (d d' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ s ↦*{d} bs ∗ s' ↦*{d'} bs' }}
    (App (Val (s @!! BytesAffineComparable.ty @!! go!"Compare"))
      (Val #(interface.mkOk BytesAffineComparable.ty #s')))
  {{ RET #(W64 (affCmp bs bs')); s ↦*{d} bs ∗ s' ↦*{d'} bs' }}

end spec

end Adt
end EtcdGrove
end Perennial
