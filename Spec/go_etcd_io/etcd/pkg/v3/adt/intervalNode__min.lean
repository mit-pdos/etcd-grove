/-
`intervalNode.min` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `CtxAt.lean`.
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

/-- `x.min(sentinel)` (internal, `successor`'s), at the root `x` (child of `p`) of a subtree
`T` that is not the leaf: the leftmost node `y` of the subtree (no left child), as its subtree
under the path of left frames from `x` down to it (`ownPathAt`, `AllL`). -/
abbrev adt.intervalNode.min.spec : Prop :=
  ∀ (x s p : Loc) (T : adt.RbT adt.Entry),
  T ≠ .leaf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownNode s 1 p x T }}
    (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"min")) (Val #s))
  {{ (y : Loc), RET #y;
      ∃ (A : adt.RbCtx adt.Entry) (ls : List (Loc × Loc)) (yp : Loc) (c : adt.RbColor)
        (ye : adt.Entry) (yr : adt.RbT adt.Entry),
        adt.ownPathAt s 1 A ls y yp (some (adt.nodeMax .leaf ye yr)) ∗
        adt.ownNode s 1 yp y (.node c .leaf ye yr) ∗
        ⌜adt.topAt A ls y yp = (x, p) ∧ A.plug (.node c .leaf ye yr) = T ∧ A.AllL⌝ }}

end spec

end EtcdGrove
end Perennial
