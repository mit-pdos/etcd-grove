/-
`(*intervalTree).insertFixup(z)` (internal; CLRS 13.3): from `FixInv` at `z`, a red-black tree with
the same in-order list.

**Proof sketch.** The loop on `FixInv`: the red-uncle case recolours and moves up; the others
rotate (`rotateLeft`/`rotateRight`, their specs) and recolour; the root blackened.

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

def intervalTree.insertFixup.spec : Prop :=
  ∀ (c : Cmp) (t s : Loc) (dq : DFrac) (C : RbCtx Entry) (z p : Loc) (tz : RbT Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ⌜(C.FixInv tz)⌝ ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      ownCtx c t s C z p tz.maxEnd ∗ ownNode c s (DFrac.own 1) p z tz }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"insertFixup")) (Val #z))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      ∃ (r : Loc) (T : RbT Entry), t.[intervalTree, go!"root"] ↦ r ∗
        ownNode c s (DFrac.own 1) s r T ∗ ⌜RbOk T ∧ T.inorder = (C.plug tz).inorder⌝ }}

end spec

end Adt
end EtcdGrove
end Perennial
