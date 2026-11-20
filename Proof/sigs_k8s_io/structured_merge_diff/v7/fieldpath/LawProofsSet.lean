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

end laws

end smd
end EtcdGrove
end Perennial
