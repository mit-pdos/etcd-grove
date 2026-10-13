/-
`intervalNode.successor` (`interval_tree.go`). Lean-first (no Rocq counterpart); see
`CtxAt.lean`.
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

/-- `z.successor(sentinel)` (internal, `Delete`'s), for a node `z` with a right child (its
right subtree `r` not the leaf: `Delete` calls it on a node with two children; the walk up the
parents of a node without one is not specified): the leftmost node `y` of `z`'s right subtree,
as its subtree under the path of left frames from `z`'s right child down to it. -/
abbrev adt.intervalNode.successor.spec : Prop :=
  ∀ (z s rp : Loc) (r : adt.RbT adt.Entry),
  r ≠ .leaf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      z.[intervalNode, go!"right"] ↦ rp ∗ adt.ownNode s 1 z rp r }}
    (App (Val (z @!! go.GoType.PointerType intervalNode.ty @!! go!"successor")) (Val #s))
  {{ (y : Loc), RET #y; z.[intervalNode, go!"right"] ↦ rp ∗
      ∃ (A : adt.RbCtx adt.Entry) (ls : List (Loc × Loc)) (yp : Loc) (c : adt.RbColor)
        (ye : adt.Entry) (yr : adt.RbT adt.Entry),
        adt.ownPathAt s 1 A ls y yp (some (adt.nodeMax .leaf ye yr)) ∗
        adt.ownNode s 1 yp y (.node c .leaf ye yr) ∗
        ⌜adt.topAt A ls y yp = (rp, z) ∧ A.plug (.node c .leaf ye yr) = r ∧ A.AllL⌝ }}

end spec

end EtcdGrove
end Perennial
