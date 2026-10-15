/-
`intervalTree.insertFixup` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Ctx.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Ctx

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

/-- `t.insertFixup(z)` (internal, `Insert`'s; CLRS's `RB-INSERT-FIXUP`), at the hole `z` of
the context `C`, its subtree `tz` red over a tree that is red-black but for `z` under a red
parent (`FixInv`): the whole tree (from the root field) red-black, with the same entries. -/
abbrev adt.intervalTree.insertFixup.spec : Prop :=
  ∀ (t s : Loc) (dq : DFrac) (C : adt.RbCtx adt.Entry) (z p : Loc) (tz : adt.RbT adt.Entry),
  C.FixInv tz →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      adt.ownCtx t s C z p tz.maxEnd ∗ adt.ownNode s 1 p z tz }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"insertFixup")) (Val #z))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      ∃ (r : Loc) (T : adt.RbT adt.Entry), t.[intervalTree, go!"root"] ↦ r ∗
        adt.ownNode s 1 s r T ∗ ⌜adt.RbOk T ∧ T.inorder = (C.plug tz).inorder⌝ }}

end spec

end EtcdGrove
end Perennial
