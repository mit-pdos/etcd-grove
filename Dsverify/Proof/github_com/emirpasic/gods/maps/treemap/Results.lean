/-
**gods' treemap, verified** (notes/gods-verified.md): the shared treemap specs
(`Dsverify/Spec/github_com/emirpasic/gods/maps/treemap/Specs.lean`, class `Hyps`) proved of gods
v1.18.1's own code (through its model `models/gods`, which only rewrites the red-black tree
iterator's `Next`/`Prev` without `goto`), over the concrete representation of `Rep.lean`: the
linked results of the red-black tree's proofs (`trees/redblacktree/`) and the treemap's, and
`hyps_true`, the instance the EPaxos and SwiftPaxos kits' statements no longer take as a premise.
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Iter
public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Lookup
public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.NewWith
public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Rotate
public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Helpers
public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Insert
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Iter
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Select

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [maps.treemap.Assumptions]

namespace trees.redblacktree

theorem Tree.rotateLeft.wp_linked : Tree.rotateLeft.spec (GF := GF) :=
  Tree.rotateLeft.wp_proof Tree.replaceNode.wp_proof
theorem Tree.rotateRight.wp_linked : Tree.rotateRight.spec (GF := GF) :=
  Tree.rotateRight.wp_proof Tree.replaceNode.wp_proof
theorem Node.uncle.wp_linked : Node.uncle.spec (GF := GF) :=
  Node.uncle.wp_proof Node.sibling.wp_proof
theorem Tree.insertCase5.wp_linked : Tree.insertCase5.spec (GF := GF) :=
  Tree.insertCase5.wp_proof Node.grandparent.wp_proof Tree.rotateLeft.wp_linked
    Tree.rotateRight.wp_linked
theorem Tree.insertCase4.wp_linked : Tree.insertCase4.spec (GF := GF) :=
  Tree.insertCase4.wp_proof Node.grandparent.wp_proof Tree.rotateLeft.wp_linked
    Tree.rotateRight.wp_linked Tree.insertCase5.wp_linked
theorem Tree.insertCase1.wp_linked : Tree.insertCase1.spec (GF := GF) :=
  Tree.insertCase1.wp_proof nodeColor.wp_proof Node.uncle.wp_linked Node.grandparent.wp_proof
    Tree.insertCase4.wp_linked
theorem Tree.Put.wp_linked : Tree.Put.spec (GF := GF) :=
  Tree.Put.wp_proof Tree.insertCase1.wp_linked
theorem Tree.Get.wp_linked : Tree.Get.spec (GF := GF) :=
  Tree.Get.wp_proof Tree.lookup.wp_proof
theorem Iterator.Next.wp_linked : Iterator.Next.spec (GF := GF) :=
  Iterator.Next.wp_proof Tree.Left.wp_proof

end trees.redblacktree

namespace maps.treemap

theorem Map.IteratorT.wp_linked : Map.IteratorT.spec (GF := GF) :=
  Map.IteratorT.wp_proof trees.redblacktree.Tree.Iterator.wp_proof
theorem Iterator.NextT.wp_linked : Iterator.NextT.spec (GF := GF) :=
  Iterator.NextT.wp_proof trees.redblacktree.Iterator.Next.wp_linked
theorem Iterator.ValueT.wp_linked : Iterator.ValueT.spec (GF := GF) :=
  Iterator.ValueT.wp_proof trees.redblacktree.Iterator.Value.wp_proof
theorem Iterator.KeyT.wp_linked : Iterator.KeyT.spec (GF := GF) :=
  Iterator.KeyT.wp_proof trees.redblacktree.Iterator.Key.wp_proof
theorem Map.Put.wp_linked : Map.Put.spec (GF := GF) isTreeMapR :=
  Map.Put.wp_proof trees.redblacktree.Tree.Put.wp_linked

/-- **The treemap specs hold of gods' code** (the file header): the shared `Hyps` at the concrete
predicates. -/
def hyps_true : Hyps GF where
  isTreeMap := isTreeMapR
  iterVal := iterValR
  ownIter := ownIterR
  NewWith_spec := NewWith.wp_proof trees.redblacktree.NewWith.wp_proof
  Put_spec := Map.Put.wp_linked
  Get_spec := Map.Get.wp_proof trees.redblacktree.Tree.Get.wp_linked
  Select_spec := Map.Select.wp_proof trees.redblacktree.NewWith.wp_proof Map.IteratorT.wp_linked
    Iterator.NextT.wp_linked Iterator.KeyT.wp_linked Iterator.ValueT.wp_linked Map.Put.wp_linked
  Iterator_spec := Map.Iterator.wp_proof Map.IteratorT.wp_linked
  iter_alloc := iter_alloc_holds
  Next_spec := Iterator.Next.wp_proof Iterator.NextT.wp_linked
  Value_spec := Iterator.Value.wp_proof Iterator.ValueT.wp_linked

end maps.treemap

end linked

end Perennial.github_com.emirpasic.gods
