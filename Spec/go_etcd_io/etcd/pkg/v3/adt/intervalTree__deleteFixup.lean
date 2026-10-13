/-
`intervalTree.deleteFixup` (`interval_tree.go`). Lean-first (no Rocq counterpart); see
`TreeDelete.lean`, `CtxAt.lean`.
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

/-- `t.deleteFixup(x)` (internal, `Delete`'s; CLRS's `RB-DELETE-FIXUP`), at the hole `x` (child
of `p`) of the context `C`, its subtree `tx` carrying an extra black over a tree that is
red-black but for that (`DelInv`); `x` may be the sentinel (the spliced node had no child), whose
`parent` is then `p` (`sentAt`): the whole tree (from the root field) red-black, with the same
entries; the sentinel's fields are any (the code writes its colour when the tree is empty). -/
abbrev adt.intervalTree.deleteFixup.spec : Prop :=
  ∀ (t s : Loc) (dq : DFrac) (C : adt.RbCtx adt.Entry) (x p : Loc) (tx : adt.RbT adt.Entry),
  C.DelInv tx →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      adt.ownCtx t s C x p tx.maxEnd ∗ adt.ownNode s 1 p x tx ∗ adt.sentAt s x p }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"deleteFixup")) (Val #x))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ adt.ownSentinel s 1 ∗
      ∃ (r : Loc) (T : adt.RbT adt.Entry), t.[intervalTree, go!"root"] ↦ r ∗
        adt.ownNode s 1 s r T ∗ ⌜adt.RbOk T ∧ T.inorder = (C.plug tx).inorder⌝ }}

end spec

end EtcdGrove
end Perennial
