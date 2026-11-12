/-
`intervalNode.updateMax` (`interval_tree.go`). Lean-first (no Rocq counterpart); see
`Ctx.lean`, `CtxAt.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.CtxAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `x.updateMax(sentinel)` (internal: the inserts, deletes and rotations), at the hole `x`
(not the sentinel) of the context `C`, whose nodes' `max`es are those of the tree with `x`'s
current `max` `m0`, given its children's `max`es (`childMax`: `none` at the sentinel): `x`'s
`max` recomputed from its end and its children's (`nodeMaxO`), and the path up to the root
with it (the loop goes up until a `max` does not change: the nodes above it are already
right). The context's frames' locations `ls` are kept (`CtxAt.lean`: `Delete` finds the node
it removes where it was, above the walk's start). -/
abbrev adt.intervalNode.updateMax.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t s : Loc) (C : adt.RbCtx adt.Entry) (ls : List (Loc × Loc)) (x p lp rp : Loc)
    (e : adt.Entry) (m0 : GoString)
    (ml mr : Option GoString),
  x ≠ s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownCtxAt K t s C ls x p (some m0) ∗
      K.ivAt x.[intervalNode, go!"iv"] (DFrac.own 1) e ∗
      K.maxAt x.[intervalNode, go!"max"] (DFrac.own 1) m0 ∗
      x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
      x.[intervalNode, go!"parent"] ↦ p ∗
      adt.childMax K s lp ml ∗ adt.childMax K s rp mr }}
    (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"updateMax")) (Val #s))
  {{ RET #(); adt.ownCtxAt K t s C ls x p (some (adt.nodeMaxO ml e mr)) ∗
      K.ivAt x.[intervalNode, go!"iv"] (DFrac.own 1) e ∗
      K.maxAt x.[intervalNode, go!"max"] (DFrac.own 1) (adt.nodeMaxO ml e mr) ∗
      x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
      x.[intervalNode, go!"parent"] ↦ p ∗
      adt.childMax K s lp ml ∗ adt.childMax K s rp mr }}

end spec

end EtcdGrove
end Perennial
