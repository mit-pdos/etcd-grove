/-
`(*intervalNode).successor(sentinel)` (internal; `Delete`'s, on a node with a right child): the
leftmost node of the right subtree, with the path to it.

**Proof sketch.** `x.right != sentinel`: `min` of the right child (its spec).

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

def intervalNode.successor.spec : Prop :=
  ∀ (c : Cmp) (z s rp : Loc) (r : RbT Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ⌜(r ≠ .leaf)⌝ ∗
      z.[intervalNode, go!"right"] ↦ rp ∗ ownNode c s (DFrac.own 1) z rp r }}
    (App (Val (z @!! go.GoType.PointerType intervalNode.ty @!! go!"successor")) (Val #s))
  {{ (y : Loc), RET #y; z.[intervalNode, go!"right"] ↦ rp ∗
      ∃ (A : RbCtx Entry) (ls : List (Loc × Loc)) (yp : Loc) (k : RbColor)
        (ye : Entry) (yr : RbT Entry),
        ownPathAt c s (DFrac.own 1) A ls y yp (some (nodeMax .leaf ye yr)) ∗
        ownNode c s (DFrac.own 1) yp y (.node k .leaf ye yr) ∗
        ⌜topAt A ls y yp = (rp, z) ∧ A.plug (.node k .leaf ye yr) = r ∧ A.AllL⌝ }}

end spec

end Adt
end EtcdGrove
end Perennial
