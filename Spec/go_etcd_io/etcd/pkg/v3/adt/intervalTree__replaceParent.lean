/-
`(*intervalTree).replaceParent(x, y)` (internal): `y` takes `x`'s place under `x`'s parent (or as
the root); `x`'s parent becomes `y`.

**Proof sketch.** The parent's child pointer (or `root`) and the two `parent` fields.

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

def intervalTree.replaceParent.spec : Prop :=
  ∀ (c : Cmp) (t s : Loc) (dq : DFrac) (C : RbCtx Entry) (ls : List (Loc × Loc)) (x p y yp : Loc)
    (mh : Option GoString) (my : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ⌜(x ≠ s → y ≠ s)⌝ ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ ownCtxAt c t s C ls x p mh ∗
      x.[intervalNode, go!"parent"] ↦ p ∗
      y.[intervalNode, go!"parent"] ↦ yp ∗ maxAt c (y.[intervalNode, go!"max"]) (DFrac.own 1) my }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"replaceParent"))
      (Val #x)) (Val #y))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ ownCtxAt c t s C ls y p (some my) ∗
      x.[intervalNode, go!"parent"] ↦ y ∗
      y.[intervalNode, go!"parent"] ↦ p ∗ maxAt c (y.[intervalNode, go!"max"]) (DFrac.own 1) my }}

end spec

end Adt
end EtcdGrove
end Perennial
