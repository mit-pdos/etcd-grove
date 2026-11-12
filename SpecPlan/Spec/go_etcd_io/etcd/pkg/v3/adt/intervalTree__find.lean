/-
`(*intervalTree).find(ivl)` (internal): the node holding exactly `ivl` (`findE`), or the sentinel,
with the path to it.

**Proof sketch.** The descent by begin, then end (the kind's `Compare`), the path grown.

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

def intervalTree.find.spec : Prop :=
  ∀ (c : Cmp) (t : Loc) (tv : intervalTree) (dq : DFrac) (T : RbT Entry) (vb ve : val)
    (db de : DFrac) (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"root"] ↦{dq} tv.root' ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} tv.sentinel' ∗
      ownNode c tv.sentinel' dq tv.sentinel' tv.root' T ∗
      keyAt c db vb b ∗ keyAt c de ve e }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"find"))
      (Val #(c.ivl vb ve)))
  {{ (n : Loc), RET #n;
      t.[intervalTree, go!"root"] ↦{dq} tv.root' ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} tv.sentinel' ∗
      keyAt c db vb b ∗ keyAt c de ve e ∗
      ∃ (p : Loc) (C : RbCtx Entry) (ls : List (Loc × Loc)) (Tz : RbT Entry),
        ownPathAt c tv.sentinel' dq C ls n p Tz.maxEnd ∗ ownNode c tv.sentinel' dq p n Tz ∗
        ⌜topAt C ls n p = (tv.root', tv.sentinel') ∧ C.plug Tz = T ∧
          match T.findE (b, e) with
          | none => Tz = .leaf
          | some z => ∃ c l r, Tz = .node c l z r⌝ }}

end spec

end Adt
end EtcdGrove
end Perennial
