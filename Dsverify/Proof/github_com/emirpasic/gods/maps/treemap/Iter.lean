/-
The proofs of gods' treemap iterator methods and `Map.Iterator` (`Internal.lean`, `Specs.lean`):
each calls the red-black tree iterator's in its `iterator` field.
-/
module

public import Dsverify.Spec.github_com.emirpasic.gods.maps.treemap.Internal
public import Dsverify.Spec.github_com.emirpasic.gods.trees.redblacktree.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.emirpasic.gods.trees.redblacktree (RB isTree treeRaw ownIterT)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions]

theorem Map.IteratorT.wp_proof (wp_it : trees.redblacktree.Tree.Iterator.spec (GF := GF)) :
    Map.IteratorT.spec (GF := GF) := by
  intro tm tr
  wp_start as Hm
  wp_auto
  wp_apply (wp_it tr)
  iapply HΦ; iexact Hm

theorem Iterator.NextT.wp_proof (wp_next : trees.redblacktree.Iterator.Next.spec (GF := GF)) :
    Iterator.NextT.spec (GF := GF) := by
  intro p tr enc cmp T h D rest cur
  wp_start as Hown
  unfold ownIterTM
  wp_auto
  wp_apply (wp_next _ tr enc cmp T h D rest cur) $$ [$Hown]
  iintro %b Hb
  wp_auto
  iapply HΦ; iexact Hb

theorem Iterator.ValueT.wp_proof (wp_value : trees.redblacktree.Iterator.Value.spec (GF := GF)) :
    Iterator.ValueT.spec (GF := GF) := by
  intro p tr enc cmp T h D rest k v
  wp_start as Hown
  unfold ownIterTM
  wp_auto
  wp_apply (wp_value _ tr enc cmp T h D rest k v) $$ [$Hown]
  iintro Hb
  wp_auto
  iapply HΦ; iexact Hb

theorem Iterator.KeyT.wp_proof (wp_key : trees.redblacktree.Iterator.Key.spec (GF := GF)) :
    Iterator.KeyT.spec (GF := GF) := by
  intro p tr enc cmp T h D rest k v
  wp_start as Hown
  unfold ownIterTM
  wp_auto
  wp_apply (wp_key _ tr enc cmp T h D rest k v) $$ [$Hown]
  iintro Hb
  wp_auto
  iapply HΦ; iexact Hb

/-! ### The shared specs (`Specs.lean`) over the concrete predicates -/

theorem Iterator.Next.wp_proof (wp_nextT : Iterator.NextT.spec (GF := GF)) :
    Iterator.Next.spec (GF := GF) ownIterR := by
  intro p rest cur
  wp_start_folded as Hown
  iunfold ownIterR at Hown
  icases Hown with ⟨%enc, %tr, %cmp, %T, %h, %D, Hown⟩
  wp_apply (wp_nextT p tr enc cmp T h D rest cur) $$ [$Hown]
  iintro %b Hb
  iapply HΦ
  cases rest with
  | nil =>
    icases Hb with ⟨%hb, Hb⟩
    isplitr; · ipureintro; exact hb
    iunfold ownIterR; iexists enc, tr, cmp, T, h, D; iexact Hb
  | cons e r =>
    icases Hb with ⟨%hb, Hb⟩
    isplitr; · ipureintro; exact hb
    iunfold ownIterR; iexists enc, tr, cmp, T, h, D; iexact Hb

theorem Iterator.Value.wp_proof (wp_valueT : Iterator.ValueT.spec (GF := GF)) :
    Iterator.Value.spec (GF := GF) ownIterR := by
  intro p rest k v
  wp_start_folded as Hown
  iunfold ownIterR at Hown
  icases Hown with ⟨%enc, %tr, %cmp, %T, %h, %D, Hown⟩
  wp_apply (wp_valueT p tr enc cmp T h D rest k v) $$ [$Hown]
  iintro Hb
  iapply HΦ
  iunfold ownIterR; iexists enc, tr, cmp, T, h, D; iexact Hb

theorem NewWith.wp_proof (wp_new : trees.redblacktree.NewWith.spec (GF := GF)) :
    NewWith.spec (GF := GF) isTreeMapR := by
  intro cmp enc
  wp_start as #Hcmp
  wp_auto
  wp_apply (wp_new cmp enc) $$ [$Hcmp]
  iintro %tr Htr
  wp_auto
  iapply HΦ
  iunfold isTreeMapR
  iexists tr
  iframe

theorem Map.Put.wp_proof (wp_put : trees.redblacktree.Tree.Put.spec (GF := GF)) :
    Map.Put.spec (GF := GF) isTreeMapR := by
  intro tm enc es k v
  wp_start as Hm
  iunfold isTreeMapR at Hm
  icases Hm with ⟨%tr, Hm, Htr⟩
  wp_auto
  wp_apply (wp_put tr enc es k v) $$ [$Htr]
  iintro Htr
  wp_auto
  iapply HΦ
  iunfold isTreeMapR
  iexists tr
  iframe

theorem Map.Get.wp_proof (wp_get : trees.redblacktree.Tree.Get.spec (GF := GF)) :
    Map.Get.spec (GF := GF) isTreeMapR := by
  intro tm enc es k
  wp_start as Hm
  iunfold isTreeMapR at Hm
  icases Hm with ⟨%tr, Hm, Htr⟩
  wp_auto
  wp_apply (wp_get tr enc es k) $$ [$Htr]
  iintro Htr
  wp_auto
  iapply HΦ
  iunfold isTreeMapR
  iexists tr
  iframe

theorem Map.Iterator.wp_proof (wp_itT : Map.IteratorT.spec (GF := GF)) :
    Map.Iterator.spec (GF := GF) isTreeMapR iterValR := by
  intro tm enc es
  wp_start_folded as Hm
  iunfold isTreeMapR at Hm
  icases Hm with ⟨%tr, Hm, Htr⟩
  wp_apply (wp_itT tm tr) $$ [$Hm]
  iintro Hm
  iapply HΦ
  iunfold isTree at Htr
  icases Htr with ⟨%cmp, %T, %h, %D, Hraw, -, %Hp⟩
  iunfold iterValR
  iexists enc, tr, cmp, T, h, D
  iframe
  ipureintro
  exact ⟨rfl, Hp.2.1⟩

end proof

end Perennial.github_com.emirpasic.gods.maps.treemap
