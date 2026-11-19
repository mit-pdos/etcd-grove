/-
**The root laws about owned sets, proved** (`v7/Laws.lean`): `ownSet_persist` (an owned trie given
up for good) and `ownSet_empty` (`&Set{}`).

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open LawProofs

mutual
theorem LawProofs.trieOwn_persist (p : Loc) : (t : Trie) → trieOwn (GF := GF) p t ⊢ |==> trieRep p t
  | .mk ms cs => by
      rw [trieOwn.eq_1, trieRep.eq_1]
      iintro ⟨%v, %es, %ns, Hp, Hes, -, #Hpel, Hns, -, Hc⟩
      imod (typedPointsto_dfractional _ _).dfractional_persist _ $$ Hp with #Hp
      imod ownSlice_persist _ _ _ $$ Hes with #Hes
      imod ownSlice_persist _ _ _ $$ Hns with #Hns
      imod LawProofs.trieOwnC_persist ns cs $$ Hc with #Hc
      imodintro
      iexists v, es, ns
      iframe #
  termination_by structural t => t
theorem LawProofs.trieOwnC_persist : (ns : List fieldpath.setNode) → (cs : List (PE × Trie)) →
    trieOwnC (GF := GF) ns cs ⊢ |==> trieRepC ns cs
  | [], [] => by rw [trieOwnC.eq_1, trieRepC.eq_1]; iintro _; imodintro; ipureintro; trivial
  | [], _ :: _ => by unfold trieOwnC; iintro %h; exact h.elim
  | _ :: _, [] => by unfold trieOwnC; iintro %h; exact h.elim
  | n :: ns, (pe, t) :: cs => by
      rw [trieOwnC.eq_2, trieRepC.eq_2]
      iintro ⟨#Hpe, Ht, Hc⟩
      imod LawProofs.trieOwn_persist n.set' t $$ Ht with #Ht
      imod LawProofs.trieOwnC_persist ns cs $$ Hc with #Hc
      imodintro
      iframe #
  termination_by structural _ cs => cs
end

theorem ownSet_persist_law_holds : ownSet_persist.law (GF := GF) := fun p S => by
  unfold ownSet isSet
  iintro ⟨%t, %h, Ht⟩
  imod LawProofs.trieOwn_persist p t $$ Ht with #Ht
  imodintro
  iexists t
  iframe #
  ipureintro; exact h

theorem ownSet_empty_law_holds : ownSet_empty.law (GF := GF) := fun p => by
  unfold ownSet
  iintro Hp
  iexists (Trie.mk [] [])
  isplitr
  · ipureintro
    refine ⟨⟨List.Pairwise.nil, List.Pairwise.nil, trivial⟩, fun q => ?_⟩
    simp only [Trie.paths, Trie.pathsC, List.not_mem_nil, and_false, exists_false, or_false,
      false_iff]
    intro hq
    change FSet.mem (FSet.ofList []) q = true at hq
    simp [FSet.mem, FSet.ofList] at hq
  rw [trieOwn.eq_1]
  iexists (zero_val fieldpath.Set'), [], []
  have h1 : (zero_val fieldpath.Set').Members'.members' = slice.nil := rfl
  have h2 : (zero_val fieldpath.Set').Children'.members' = slice.nil := rfl
  rw [h1, h2, isPEL.eq_1, trieOwnC.eq_1]
  iframe
  ihave Hn1 := ownSlice_nil (V := fieldpath.PathElement) (GF := GF) (DFrac.own 1)
  ihave Hn2 := ownSlice_nil (V := fieldpath.setNode) (GF := GF) (DFrac.own 1)
  ihave Hc1 := ownSliceCap_nil (V := fieldpath.PathElement) (GF := GF)
  ihave Hc2 := ownSliceCap_nil (V := fieldpath.setNode) (GF := GF)
  iframe #

end laws
end smd
end EtcdGrove
end Perennial
