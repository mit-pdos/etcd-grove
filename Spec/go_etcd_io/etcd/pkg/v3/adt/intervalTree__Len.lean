/-
`(*intervalTree).Len()`: the entry count.

**Users.** None in etcd's verified code (kept: verified before). **Proof sketch.** Reads `count`.
**Changes.** At any fraction and key kind. **Margin.** None.
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

def intervalTree.Len.spec : Prop :=
  ∀ (c : Cmp) (t : Loc) (L : List Entry) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ivt c t L dq }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 L.length); ivt c t L dq }}

end spec

end Adt
end EtcdGrove
end Perennial
