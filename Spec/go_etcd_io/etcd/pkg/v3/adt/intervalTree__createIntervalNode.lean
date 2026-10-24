/-
`intervalTree.createIntervalNode` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Ctx.lean`.
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

/-- `t.createIntervalNode(ivl, v)` (internal, `Insert`'s), over the keys `K` (the interval's
values holding its keys read-only: the node keeps them): a new red node with the entry, its
`max` the interval's end, its links the sentinel (read from the tree struct). -/
abbrev adt.intervalTree.createIntervalNode.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t s : Loc) (dq : DFrac) (vb ve : val) (b e : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ K.keyAt .discard vb b ∗ K.keyAt .discard ve e }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"createIntervalNode"))
      (Val #(K.ivl vb ve))) (Val #v))
  {{ (z : Loc), RET #z; t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ ⌜z ≠ null⌝ ∗
      K.ivAt z.[intervalNode, go!"iv"] (DFrac.own 1) ((b, e), v) ∗
      K.maxAt z.[intervalNode, go!"max"] (DFrac.own 1) e ∗
      z.[intervalNode, go!"left"] ↦ s ∗ z.[intervalNode, go!"right"] ↦ s ∗
      z.[intervalNode, go!"parent"] ↦ s ∗ z.[intervalNode, go!"c"] ↦ adt.colorW .red }}

end spec

end EtcdGrove
end Perennial
