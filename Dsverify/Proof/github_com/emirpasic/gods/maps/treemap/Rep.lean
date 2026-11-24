/-
gods' treemap's representation predicates (notes/gods-verified.md), the concrete ones the shared
specs (`Dsverify/Spec/github_com/emirpasic/gods/maps/treemap/Specs.lean`, class `Hyps`) are proved
over: a `*Map` is its `*Tree` (`redblacktree.isTree`, `trees/redblacktree/Defs.lean`); an iterator
value is the red-black tree iterator before its first entry, with the tree it owns; an iterator at
`p` is the red-black tree iterator in its `iterator` field (`redblacktree.ownIterT`).
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.emirpasic.gods.trees.redblacktree (RB isTree treeRaw ownIterT iterAt treeRaw_pure)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions]

/-- The `*Map` at `tm`: its tree holds the entries `es`. -/
def isTreeMapR (tm : Loc) (enc : w64 → GoInterface) (es : Entries) : IProp GF :=
  iprop(∃ tr : Loc, tm ↦ Map.mk tr ∗ isTree tr enc es)

/-- An `Iterator` value `m.Iterator()` returned: before the first entry of the tree it owns. -/
def iterValR (v : github_com.emirpasic.gods.maps.treemap.Iterator) (es : Entries) : IProp GF :=
  iprop(∃ (enc : w64 → GoInterface) (tr : Loc) (cmp : GoFunc) (T : RB GoInterface)
      (h : Loc → trees.redblacktree.Node) (D : List Loc),
    ⌜v.iterator' = trees.redblacktree.Iterator.mk tr null (W8 0) ∧ T.entries = es⌝ ∗
    treeRaw tr enc cmp T h D)

/-- The iterator at `p`, its tree fixed: the red-black tree iterator in its `iterator` field. -/
def ownIterTM (p tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (h : Loc → trees.redblacktree.Node) (D : List Loc) (rest : Entries)
    (cur : Option (w64 × GoInterface)) : IProp GF :=
  ownIterT (structFieldRef github_com.emirpasic.gods.maps.treemap.Iterator go!"iterator" p) tr enc
    cmp T h D rest cur

/-- The iterator at `p`, with `rest` still to visit and the current entry `cur`. -/
def ownIterR (p : Loc) (rest : Entries) (cur : Option (w64 × GoInterface)) : IProp GF :=
  iprop(∃ (enc : w64 → GoInterface) (tr : Loc) (cmp : GoFunc) (T : RB GoInterface)
      (h : Loc → trees.redblacktree.Node) (D : List Loc),
    ownIterTM p tr enc cmp T h D rest cur)

/-- **The iterator law** (`iter_alloc.law` of the shared specs). -/
theorem iter_alloc_holds : iter_alloc.law (GF := GF) iterValR ownIterR := by
  intro p v es
  iintro ⟨Hp, Hv⟩
  iunfold iterValR at Hv
  icases Hv with ⟨%enc, %tr, %cmp, %T, %h, %D, %Hv, Hraw⟩
  obtain ⟨hv, hes⟩ := Hv
  iStructNamed Hp
  iunfold ownIterR
  iexists enc, tr, cmp, T, h, D
  unfold ownIterTM ownIterT
  iexists null, W8 0
  rw [← hv]
  iframe
  ipureintro
  left; exact ⟨rfl, rfl, hes.symm⟩

end defs

end Perennial.github_com.emirpasic.gods.maps.treemap
