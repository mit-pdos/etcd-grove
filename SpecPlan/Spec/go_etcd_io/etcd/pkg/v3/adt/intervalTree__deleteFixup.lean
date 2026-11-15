/-
`(*intervalTree).deleteFixup(x)` (internal; CLRS 13.4): from `DelInv` at `x` (possibly the
sentinel, whose `parent` `Delete` set), a red-black tree with the same in-order list.

**Proof sketch.** The loop on `DelInv`: the four cases, with rotations (their specs) and
recolouring; `x` blackened at the exit.

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

def intervalTree.deleteFixup.spec : Prop :=
  ∀ (c : Cmp) (t s : Loc) (dq : DFrac) (C : RbCtx Entry) (x p : Loc) (tx : RbT Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ⌜(C.DelInv tx)⌝ ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      ownCtx c t s C x p tx.maxEnd ∗ ownNode c s (DFrac.own 1) p x tx ∗ sentAt s x p }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"deleteFixup")) (Val #x))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ ownSentinel s (DFrac.own 1) ∗
      ∃ (r : Loc) (T : RbT Entry), t.[intervalTree, go!"root"] ↦ r ∗
        ownNode c s (DFrac.own 1) s r T ∗ ⌜RbOk T ∧ T.inorder = (C.plug tx).inorder⌝ }}

end spec

end Adt
end EtcdGrove
end Perennial
