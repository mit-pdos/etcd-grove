/-
`(*intervalNode).min(sentinel)` (internal): the leftmost node of a non-empty subtree, with the path
down to it (only left frames).

**Proof sketch.** The loop on `left`, the path grown frame by frame (`ownPathAt`).

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

def intervalNode.min.spec : Prop :=
  ∀ (c : Cmp) (x s p : Loc) (T : RbT Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ⌜(T ≠ .leaf)⌝ ∗ ownNode c s (DFrac.own 1) p x T }}
    (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"min")) (Val #s))
  {{ (y : Loc), RET #y;
      ∃ (A : RbCtx Entry) (ls : List (Loc × Loc)) (yp : Loc) (k : RbColor)
        (ye : Entry) (yr : RbT Entry),
        ownPathAt c s (DFrac.own 1) A ls y yp (some (nodeMax .leaf ye yr)) ∗
        ownNode c s (DFrac.own 1) yp y (.node k .leaf ye yr) ∗
        ⌜topAt A ls y yp = (x, p) ∧ A.plug (.node k .leaf ye yr) = T ∧ A.AllL⌝ }}

end spec

end Adt
end EtcdGrove
end Perennial
