/-
`intervalTree.Len` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
Pending: the interval tree's contract, proved in unit 4 (the tree's proof); until then a
hypothesis of every result that reaches it (`?` in `etc/link-lean-first-adt.txt`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Holes

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

/-- `x.visit(iv, sentinel, nv)` (internal, `Visit`'s), on the subtree at `x` (child of `p`)
holding `Tx` (sorted), at a fraction `q`, for a query that is not empty-and-finite (`b = ""` or
`b < e`): calls the visitor on exactly the nodes whose entries overlap the query, in order; the
visitor keeps their `iv` fields (recorded in `I`), and goes on (`nodeVisitorOk`). Returns
`true`, the subtree with those fields lent out (`ownNodeH`, `ns` the nodes). The visitor is told
it is called on the entries of `S` in order: the entries visited before (`acc`) and this
subtree's visited ones are a prefix of `S`. -/
abbrev adt.intervalNode.visit.spec : Prop :=
  ∀ (s : Loc) (q : Qp) (p x : Loc) (Tx : adt.RbT adt.Entry) (ivp : Loc) (dq : DFrac)
    (b e : GoString) (nv : GoFunc) (S : List adt.Entry) (I : List (Loc × adt.Entry) → IProp GF)
    (acc : List (Loc × adt.Entry)),
  adt.IvSorted Tx.inorder → (b = go!"" ∨ adt.affLt b e) →
  acc.map Prod.snd ++ adt.stab (b, e) Tx.inorder <+: S →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownNode s q p x Tx ∗ ivp ↦{dq} adt.affIvl b e ∗ adt.nodeVisitorOk q S nv I ∗ I acc }}
    (App (App (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"visit"))
      (Val #ivp)) (Val #s)) (Val #nv))
  {{ RET #true; ∃ ns : List Loc, adt.ownNodeH s q (b, e) p x Tx ns ∗
      ivp ↦{dq} adt.affIvl b e ∗ I (acc ++ ns.zip (adt.stab (b, e) Tx.inorder)) }}

end spec

end EtcdGrove
end Perennial
