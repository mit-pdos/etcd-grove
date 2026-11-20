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
non-empty prefixes (`PathSet.card_nodes.law`). -/
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

theorem PathSet_card_nodes_law_holds : PathSet.card_nodes.law := PathSet_card_nodes_of_ne

namespace fpN

theorem dedupL_length_le {α : Type} [DecidableEq α] : (l : List α) → (FSet.dedupL l).length ≤ l.length
  | [] => by simp [FSet.dedupL]
  | x :: xs => by
    have := dedupL_length_le xs
    unfold FSet.dedupL; split <;> simp <;> omega

/-- `NewSet`'s count: the set of `k` paths has at most `k` members. -/
theorem card_ofList_le (l : List Path) : (PathSet.ofList l).card ≤ l.length := by
  show (FSet.dedupL (l.filter _)).length ≤ _
  exact Nat.le_trans (dedupL_length_le _) (List.length_filter_le _ _)

/-- `NewSet`'s step: one more path inserted. -/
theorem ofList_take_succ (ps : List Path) (k : Nat) (p : Path) (h : ps[k]? = some p) :
    PathSet.union (PathSet.ofList (ps.take k)) (PathSet.single p) = PathSet.ofList (ps.take (k + 1)) := by
  rw [List.take_add_one, h]
  show FSet.ofList _ = FSet.ofList _
  simp only [Option.toList_some, List.filter_append]

end fpN

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

theorem under_deep (A : PathSet) (e : PE) : A.deep.under e = A.under e := by
  apply FSet.ext'; intro q
  rw [mem_under, mem_under, mem_deep]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨h1, h2, ?_⟩
    match q, h1 with
    | _ :: _, _ => simp

/-- No head, nothing below it. -/
theorem under_empty (A : PathSet) (e : PE) (h : e ∉ A.heads) : A.under e = PathSet.ofList [] := by
  apply FSet.ext'; intro q
  rw [mem_under, PathSet_mem_ofList_law_holds]
  constructor
  · rintro ⟨h1, h2⟩; exact absurd ((mem_heads A e).2 ⟨q, h1, h2⟩) h
  · rintro ⟨h1, -⟩; simp at h1

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

mutual
theorem fpS.trieOwn_persist (p : Loc) : (t : Trie) → trieOwn (GF := GF) p t ⊢ |==> trieRep p t
  | .mk ms cs => by
      rw [trieOwn.eq_1, trieRep.eq_1]
      iintro ⟨%v, %es, %ns, Hp, Hes, -, #Hpel, Hns, -, Hc⟩
      imod (typedPointsto_dfractional _ _).dfractional_persist _ $$ Hp with #Hp
      imod ownSlice_persist _ _ _ $$ Hes with #Hes
      imod ownSlice_persist _ _ _ $$ Hns with #Hns
      imod fpS.trieOwnC_persist ns cs $$ Hc with #Hc
      imodintro
      iexists v, es, ns
      iframe #
  termination_by structural t => t
theorem fpS.trieOwnC_persist : (ns : List fieldpath.setNode) → (cs : List (PE × Trie)) →
    trieOwnC (GF := GF) ns cs ⊢ |==> trieRepC ns cs
  | [], [] => by rw [trieOwnC.eq_1, trieRepC.eq_1]; iintro _; imodintro; ipureintro; trivial
  | [], _ :: _ => by unfold trieOwnC; iintro %h; exact h.elim
  | _ :: _, [] => by unfold trieOwnC; iintro %h; exact h.elim
  | n :: ns, (pe, t) :: cs => by
      rw [trieOwnC.eq_2, trieRepC.eq_2]
      iintro ⟨#Hpe, Ht, Hc⟩
      imod fpS.trieOwn_persist n.set' t $$ Ht with #Ht
      imod fpS.trieOwnC_persist ns cs $$ Hc with #Hc
      imodintro
      iframe #
  termination_by structural _ cs => cs
end

/-- An owned set given up for good (the root's `ownSet_persist`, restated here). -/
theorem fpS.ownSet_persist (p : Loc) (S : PathSet) : ownSet (GF := GF) p S ⊢ |==> isSet p S := by
  unfold ownSet isSet
  iintro ⟨%t, %h, Ht⟩
  imod fpS.trieOwn_persist p t $$ Ht with #Ht
  imodintro
  iexists t
  iframe #
  ipureintro; exact h

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

/-- Persistent paths are paths lent at the discarded fraction (`NewSet`'s argument). -/
theorem fpN.isPaths_isPathsF : (ss : List GoSlice) → (ps : List Path) →
    isPaths (GF := GF) ss ps ⊣⊢ isPathsF ss DFrac.discard ps
  | [], [] => by unfold isPaths isPathsF; exact .rfl
  | [], _ :: _ => by unfold isPaths isPathsF; exact .rfl
  | _ :: _, [] => by unfold isPaths isPathsF; exact .rfl
  | s :: ss, p :: ps => by
    unfold isPaths isPathsF
    exact sep_congr (isPath_isPathF_law_holds s p) (fpN.isPaths_isPathsF ss ps)

theorem fpN.isPathsF_length (dq : DFrac) : (ss : List GoSlice) → (ps : List Path) →
    isPathsF (GF := GF) ss dq ps ⊢ ⌜ss.length = ps.length⌝
  | [], [] => by iintro _; ipureintro; rfl
  | [], _ :: _ => by unfold isPathsF; iintro %h; exact h.elim
  | _ :: _, [] => by unfold isPathsF; iintro %h; exact h.elim
  | s :: ss, p :: ps => by
    unfold isPathsF
    iintro ⟨-, H⟩
    ihave %h := fpN.isPathsF_length dq ss ps $$ H
    ipureintro; simp [h]

/-- The `k`-th path of lent paths, and the way back. -/
theorem fpN.isPathsF_acc (dq : DFrac) : (ss : List GoSlice) → (ps : List Path) → (k : Nat) →
    (s0 : GoSlice) → (p0 : Path) → ss[k]? = some s0 → ps[k]? = some p0 →
    isPathsF (GF := GF) ss dq ps ⊢ isPathF s0 dq p0 ∗ (isPathF s0 dq p0 -∗ isPathsF ss dq ps)
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | s :: ss, p :: ps, 0, s0, p0, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    unfold isPathsF
    iintro ⟨H1, H2⟩
    iframe
    iintro H1; iframe
  | s :: ss, p :: ps, k + 1, s0, p0, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    unfold isPathsF
    iintro ⟨H1, H2⟩
    icases fpN.isPathsF_acc dq ss ps k s0 p0 h1 h2 $$ H2 with ⟨H, Hb⟩
    iframe
    iintro H; iframe; iapply Hb; iexact H

end laws

end smd
end EtcdGrove
end Perennial
