/-
`intervalTree.rotateLeft` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Ctx.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.CtxAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `t.rotateLeft(x)` (internal, `insertFixup`'s and `deleteFixup`'s), at the hole `x` of the
context `C` with its right child `y` (CLRS's `LEFT-ROTATE`; the code returns early without
one): `y` takes `x`'s place, `x` becomes its left child with `y`'s left subtree on its right;
the two nodes' `max`es recomputed (`updateMax`, through `replaceParent`'s on the path above,
which ends as it was). The two nodes' fields are explicit (the callers know their pointers),
their other subtrees owned whole; the context's frames' locations `ls` are kept, and `x`'s
fields are given back as such (`deleteFixup` goes on below `x`). -/
abbrev adt.intervalTree.rotateLeft.spec : Prop :=
  ∀ (t s : Loc) (dq : DFrac) (C : adt.RbCtx adt.Entry) (ls : List (Loc × Loc))
    (x p y ap bp dp : Loc)
    (cx cy : adt.RbColor) (a b d : adt.RbT adt.Entry) (xe ye : adt.Entry),
  x ≠ s ∧ x ≠ null → y ≠ s ∧ y ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      adt.ownCtxAt t s C ls x p (some (adt.nodeMax a xe (.node cy b ye d))) ∗
      x.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl xe.1.1 xe.1.2, Val' := xe.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax a xe (.node cy b ye d)) ∗
      x.[intervalNode, go!"left"] ↦ ap ∗ x.[intervalNode, go!"right"] ↦ y ∗
      x.[intervalNode, go!"parent"] ↦ p ∗ x.[intervalNode, go!"c"] ↦ adt.colorW cx ∗
      y.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl ye.1.1 ye.1.2, Val' := ye.2 } : IntervalValue) ∗
      y.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax b ye d) ∗
      y.[intervalNode, go!"left"] ↦ bp ∗ y.[intervalNode, go!"right"] ↦ dp ∗
      y.[intervalNode, go!"parent"] ↦ x ∗ y.[intervalNode, go!"c"] ↦ adt.colorW cy ∗
      adt.ownNode s 1 x ap a ∗ adt.ownNode s 1 y bp b ∗ adt.ownNode s 1 y dp d }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"rotateLeft")) (Val #x))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      adt.ownCtxAt t s C ls y p (some (adt.nodeMax (.node cx a xe b) ye d)) ∗
      y.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl ye.1.1 ye.1.2, Val' := ye.2 } : IntervalValue) ∗
      y.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax (.node cx a xe b) ye d) ∗
      y.[intervalNode, go!"left"] ↦ x ∗ y.[intervalNode, go!"right"] ↦ dp ∗
      y.[intervalNode, go!"parent"] ↦ p ∗ y.[intervalNode, go!"c"] ↦ adt.colorW cy ∗
      x.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl xe.1.1 xe.1.2, Val' := xe.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax a xe b) ∗
      x.[intervalNode, go!"left"] ↦ ap ∗ x.[intervalNode, go!"right"] ↦ bp ∗
      x.[intervalNode, go!"parent"] ↦ y ∗ x.[intervalNode, go!"c"] ↦ adt.colorW cx ∗
      adt.ownNode s 1 x ap a ∗ adt.ownNode s 1 x bp b ∗ adt.ownNode s 1 y dp d }}

end spec

end EtcdGrove
end Perennial
