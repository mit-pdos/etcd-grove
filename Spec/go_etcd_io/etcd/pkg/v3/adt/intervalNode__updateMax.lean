/-
`(*intervalNode).updateMax(sentinel)` (internal): recomputes the node's `max` from its end and
its children's, and its ancestors' while they change.

**Proof sketch.** The loop up the path (`ownCtxAt`'s frames): each step `Compare`s (the kind's spec)
and stops when the max is unchanged (the frames above are then right).

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

def intervalNode.updateMax.spec : Prop :=
  ∀ (c : Cmp) (t s : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (x p lp rp : Loc)
    (e : Entry) (m0 : GoString)
    (ml mr : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ⌜(x ≠ s)⌝ ∗
      ownCtxAt c t s C ls x p (some m0) ∗
      ivAt c (x.[intervalNode, go!"iv"]) (DFrac.own 1) e ∗
      maxAt c (x.[intervalNode, go!"max"]) (DFrac.own 1) m0 ∗
      x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
      x.[intervalNode, go!"parent"] ↦ p ∗
      childMax c s lp ml ∗ childMax c s rp mr }}
    (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"updateMax")) (Val #s))
  {{ RET #(); ownCtxAt c t s C ls x p (some (nodeMaxO ml e mr)) ∗
      ivAt c (x.[intervalNode, go!"iv"]) (DFrac.own 1) e ∗
      maxAt c (x.[intervalNode, go!"max"]) (DFrac.own 1) (nodeMaxO ml e mr) ∗
      x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
      x.[intervalNode, go!"parent"] ↦ p ∗
      childMax c s lp ml ∗ childMax c s rp mr }}

end spec

end Adt
end EtcdGrove
end Perennial
