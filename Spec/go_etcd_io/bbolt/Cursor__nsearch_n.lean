/-
`Cursor.nsearch` on a node (bbolt, internal to U6d of `notes/bbolt-proof-plan.md`): the stack's
top element refers to a live node of the writer; its index becomes the search index of the key
in the node's entries (`wsIdx`). Proof: `Proof/go_etcd_io/bbolt/Cursor__nsearch_n.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WtxHeap
public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.bbolt.Read.Src

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `c.nsearch(key)` when the stack's top element `e` is the live node `e.node'` (record `rn`,
sorted live entries): its index becomes `wsIdx rn.ws kb`. The node's and the key's bytes are read
through the view's cells. -/
abbrev Cursor.nsearch_n.spec : Prop :=
  ∀ (c b : Loc) (stk : GoSlice) (els : List elemRef) (e : elemRef) (v : View) (bl : Loc)
    (rn : NRec) (q : Qp) (key : GoSlice) (kr : KeyR) (kb : List w8),
  e.node' ≠ null → wsSorted rn.ws → wsLive rn.ws → 0 < v.base.addr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ c ↦ Cursor.mk b stk ∗
      stk ↦* (els ++ [e]) ∗ objOwn v e.node' (DFrac.own 1) true (.node bl rn) ∗ viewCells q v ∗
      keyR v key kr kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"nsearch")) (Val #key))
  {{ RET #(); c ↦ Cursor.mk b stk ∗
      stk ↦* (els ++ [⟨e.page', e.node', W64 (wsIdx rn.ws kb : Int)⟩]) ∗
      objOwn v e.node' (DFrac.own 1) true (.node bl rn) ∗ viewCells q v ∗ keyR v key kr kb }}

/-- **`nsearch` on a node at a fraction** (U6w): `spec` with the node's object at `qn` (a
fraction of the writer's heap, `wtxWQ`). `spec` is its case `qn = 1`. -/
abbrev Cursor.nsearch_n.specQ : Prop :=
  ∀ (c b : Loc) (stk : GoSlice) (els : List elemRef) (e : elemRef) (v : View) (bl : Loc)
    (rn : NRec) (qn : Qp) (q : Qp) (key : GoSlice) (kr : KeyR) (kb : List w8),
  e.node' ≠ null → wsSorted rn.ws → wsLive rn.ws → 0 < v.base.addr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ c ↦ Cursor.mk b stk ∗
      stk ↦* (els ++ [e]) ∗ objOwn v e.node' (DFrac.own qn) true (.node bl rn) ∗ viewCells q v ∗
      keyR v key kr kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"nsearch")) (Val #key))
  {{ RET #(); c ↦ Cursor.mk b stk ∗
      stk ↦* (els ++ [⟨e.page', e.node', W64 (wsIdx rn.ws kb : Int)⟩]) ∗
      objOwn v e.node' (DFrac.own qn) true (.node bl rn) ∗ viewCells q v ∗ keyR v key kr kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
