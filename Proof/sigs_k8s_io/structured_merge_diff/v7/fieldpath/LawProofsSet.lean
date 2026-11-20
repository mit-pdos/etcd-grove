/-
**`fieldpath`'s set laws, proved** (`fieldpath/Vocab.lean`): a set's two halves (`isSet_split`),
no set holds the empty path (`isSet_ne`, `ownSet_ne`), and a set counts at most its trie's nodes
(`PathSet.card_nodes`, for sets without the empty path).

Prove phase (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsTrie
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

/-- A set without the empty path counts at most its trie's nodes: each path is one of its own
non-empty prefixes. (`PathSet.card_nodes.law` as stated, without `[] ∉ S`, is false: `{[]}` has
one member and no nodes.) -/
theorem PathSet_card_nodes_of_ne (S : PathSet) (hne : [] ∉ S) : S.card ≤ S.nodes.card := by
  apply FSet.card_le_of_subset
  intro q hq
  unfold PathSet.nodes
  rw [FSet.mem_bind']
  refine ⟨q, hq, ?_⟩
  have hl : 0 < q.length := by
    cases q with
    | nil => exact absurd hq hne
    | cons _ _ => simp
  unfold Path.nePrefixes
  rw [List.mem_map]
  refine ⟨q.length - 1, List.mem_range.2 (by omega), ?_⟩
  rw [Nat.sub_add_cancel hl, List.take_length]

namespace fpS
open fpC

theorem nePrefixes_single (e : PE) : Path.nePrefixes [e] = [[e]] := rfl

theorem tops_union (A B : PathSet) : (PathSet.union A B).tops = FSet.union A.tops B.tops := by
  apply FSet.ext'; intro e; rw [FSet.mem_union', mem_tops, mem_tops, mem_tops, mem_punion]
theorem deep_union (A B : PathSet) : (PathSet.union A B).deep = PathSet.union A.deep B.deep := by
  apply FSet.ext'; intro q
  rw [mem_deep, mem_punion, mem_punion, mem_deep, mem_deep]; grind
theorem tops_inter (A B : PathSet) : (PathSet.inter A B).tops = FSet.inter A.tops B.tops := by
  apply FSet.ext'; intro e; rw [FSet.mem_inter', mem_tops, mem_tops, mem_tops, mem_pinter]
theorem deep_inter (A B : PathSet) : (PathSet.inter A B).deep = PathSet.inter A.deep B.deep := by
  apply FSet.ext'; intro q
  rw [mem_deep, mem_pinter, mem_pinter, mem_deep, mem_deep]; grind
theorem tops_diff (A B : PathSet) : (PathSet.diff A B).tops = FSet.diff A.tops B.tops := by
  apply FSet.ext'; intro e; rw [FSet.mem_diff', mem_tops, mem_tops, mem_tops, mem_pdiff]
theorem deep_diff (A B : PathSet) : (PathSet.diff A B).deep = PathSet.diff A.deep B := by
  apply FSet.ext'; intro q
  rw [mem_deep, mem_pdiff, mem_pdiff, mem_deep]; grind
theorem tops_rdiff (A B : PathSet) : (PathSet.rdiff A B).tops = FSet.diff A.tops B.tops := by
  apply FSet.ext'; intro e
  rw [FSet.mem_diff', mem_tops, mem_tops, mem_tops, mem_rdiff, nePrefixes_single]
  simp
theorem deep_rdiff (A B : PathSet) : (PathSet.rdiff A B).deep = PathSet.rdiff A.deep B := by
  apply FSet.ext'; intro q
  rw [mem_deep, mem_rdiff, mem_rdiff, mem_deep]; grind

theorem ne_union {A B : PathSet} (hA : [] ∉ A) (hB : [] ∉ B) : [] ∉ PathSet.union A B := by
  rw [mem_punion]; grind
theorem ne_inter {A B : PathSet} (hA : [] ∉ A) : [] ∉ PathSet.inter A B := by
  rw [mem_pinter]; grind
theorem ne_diff {A B : PathSet} (hA : [] ∉ A) : [] ∉ PathSet.diff A B := by
  rw [mem_pdiff]; grind
theorem ne_rdiff {A B : PathSet} (hA : [] ∉ A) : [] ∉ PathSet.rdiff A B := by
  rw [mem_rdiff]; grind

end fpS

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem isSet_ne_law_holds : isSet_ne.law (GF := GF) := fun p S => by
  iintro H
  ihave ⟨%v, -, -, -, %h⟩ := (fpC.isSet_view p S).1 $$ H
  ipureintro; exact h

theorem isSet_split_law_holds : isSet_split.law (GF := GF) := fun p S => by
  iintro H
  ihave ⟨%v, #Hp, Hm, Hc, -⟩ := (fpC.isSet_view p S).1 $$ H
  iStructNamed Hp
  isplitl [Hm]
  · unfold isPESet
    iexists v.Members'
    iframe
    iexact Members
  · unfold isNodes
    iexists v.Children'
    iframe
    iexact Children

theorem ownSet_ne_law_holds : ownSet_ne.law (GF := GF) := fun p S => by
  iintro H
  iunfold ownSet at H
  icases H with ⟨%t, %ht, Ht⟩
  isplitr
  · ipureintro
    intro h
    exact fpC.paths_ne_nil t ((ht.2 []).2 h)
  · iunfold ownSet
    iexists t
    iframe
    ipureintro; exact ht

/-- **A set from its two halves**: a set struct, persistent, whose members are `S`'s tops and
whose children are `S`'s deep paths. -/
theorem fpS.isSet_of_parts (r : Loc) (v : fieldpath.Set') (S : PathSet) (T : FSet PE) (D : PathSet)
    (hT : S.tops = T) (hD : S.deep = D) (hne : [] ∉ S) :
    r ↦□ v ∗ isPESetV (GF := GF) v.Members' DFrac.discard T ∗ isNodesV v.Children' D ⊢ isSet r S := by
  iintro ⟨#Hr, Hm, Hc⟩
  iapply (fpC.isSet_view r S).2
  iexists v
  rw [hT, hD]
  isplit
  · iexact Hr
  iframe
  ipureintro; exact hne

end laws

end smd
end EtcdGrove
end Perennial
