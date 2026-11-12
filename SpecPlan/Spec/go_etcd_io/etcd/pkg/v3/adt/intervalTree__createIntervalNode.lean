/-
`(*intervalTree).createIntervalNode(ivl, val)` (internal): a fresh red node, its children and
parent the sentinel, its `max` the interval's end.

**Proof sketch.** A struct literal.

**Changes** from `specs-ref`'s file: at a key kind `c` (was a key representation `K` with
its comparison contract); pure premises in the precondition.

**Margin.** Mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.adt.Internal

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

def intervalTree.createIntervalNode.spec : Prop :=
  ∀ (c : Cmp) (t s : Loc) (dq : DFrac) (vb ve : val) (b e : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ keyAt c DFrac.discard vb b ∗ keyAt c DFrac.discard ve e }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"createIntervalNode"))
      (Val #(c.ivl vb ve))) (Val #v))
  {{ (z : Loc), RET #z; t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ ⌜z ≠ null⌝ ∗
      ivAt c (z.[intervalNode, go!"iv"]) (DFrac.own 1) ((b, e), v) ∗
      maxAt c (z.[intervalNode, go!"max"]) (DFrac.own 1) e ∗
      z.[intervalNode, go!"left"] ↦ s ∗ z.[intervalNode, go!"right"] ↦ s ∗
      z.[intervalNode, go!"parent"] ↦ s ∗ z.[intervalNode, go!"c"] ↦ colorW .red }}

end spec

end Adt
end EtcdGrove
end Perennial
