/-
`(*intervalNode).color(sentinel)` (internal): black at the sentinel, else the node's colour.

**Proof sketch.** The comparison with the sentinel; the `c` field.

**Changes** from `specs-ref`'s file: at a key kind `c` (was a key representation `K` with
its comparison contract); pure premises in the precondition.

**Margin.** Mirrors the code.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Internal

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

def intervalNode.color.spec : Prop :=
  ∀ (c : Cmp) (x s : Loc) (k : RbColor) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ colorAt s x k dq }}
    (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"color")) (Val #s))
  {{ RET #(colorW k); colorAt s x k dq }}

end spec

end Adt
end EtcdGrove
end Perennial
