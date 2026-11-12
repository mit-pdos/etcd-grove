/-
`Cursor.nsearch` on a page (bbolt, internal to U6 of `notes/bbolt-proof-plan.md`): the stack's
top element refers to a leaf page (no node); its index becomes the first leaf key not below the
search key. Proof: `Proof/go_etcd_io/bbolt/Cursor__nsearch_p.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Tree
public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The search index of `k` in the leaf page `pg`: the number of its leading keys below `k`. -/
def pageSeekIdx (pg : List w8) (k : List w8) : Nat :=
  ((List.range (pageCount pg)).takeWhile fun i => decide (go.GoStringLt (leafKey pg i) k)).length

/-- `c.nsearch(key)` when the stack's top element `e` is the leaf page `pg` at `p` (no node): its
index becomes `pageSeekIdx pg kb`. -/
abbrev Cursor.nsearch_p.spec : Prop :=
  ∀ (c b : Loc) (stk : GoSlice) (els : List elemRef) (e : elemRef) (dq : DFrac) (pg : List w8)
    (key : GoSlice) (dk : DFrac) (kb : List w8),
  e.node' = null → pageFlags pg = leafPageFlag → leafWF pg pg.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ c ↦ Cursor.mk b stk ∗
      stk ↦* (els ++ [e]) ∗ bytesPointsto e.page' dq pg ∗ key ↦*{dk} kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"nsearch")) (Val #key))
  {{ RET #(); c ↦ Cursor.mk b stk ∗
      stk ↦* (els ++ [⟨e.page', e.node', W64 (pageSeekIdx pg kb : Int)⟩]) ∗
      bytesPointsto e.page' dq pg ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
