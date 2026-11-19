/-
**The root laws about map literals, proved** (`v7/Laws.lean`): `isIface_ofMap` and `isMF_intro`
(a Go map literal's entries, sorted by `kvsOf`), with the facts about `insertKV`/`kvsOf` they rest
on.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Intro
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Pure
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace LawProofs

/-! ## Sorted association lists, built by `insertKV` -/

theorem keysSorted_iff_pairwise {α : Type} : ∀ (l : List (GoString × α)),
    keysSorted l = true ↔ l.Pairwise (fun a b => gsLt a.1 b.1 = true)
  | [] => by simp [keysSorted]
  | [a] => by simp [keysSorted]
  | (k, v) :: (k', v') :: rest => by
      have ih := keysSorted_iff_pairwise ((k', v') :: rest)
      constructor
      · intro h
        have hh := h
        simp only [keysSorted, Bool.and_eq_true] at hh
        refine List.Pairwise.cons ?_ (ih.1 hh.2)
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact hh.1
        · obtain ⟨kb, vb⟩ := b
          exact keysSorted_head_lt h kb vb (List.mem_cons_of_mem _ hb')
      · intro h
        simp only [keysSorted, Bool.and_eq_true]
        rw [List.pairwise_cons] at h
        exact ⟨h.1 _ List.mem_cons_self, ih.2 h.2⟩

theorem mem_insertKV {α : Type} {k : GoString} {v : α} {e : GoString × α} :
    ∀ {l : List (GoString × α)}, e ∈ insertKV k v l → e = (k, v) ∨ e ∈ l
  | [], h => by simp [insertKV] at h; exact Or.inl h
  | (k', v') :: rest, h => by
      unfold insertKV at h
      split at h
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · split at h
        · rcases List.mem_cons.1 h with h | h
          · exact Or.inl h
          · exact Or.inr h
        · rcases List.mem_cons.1 h with h | h
          · exact Or.inr (h ▸ List.mem_cons_self)
          · rcases mem_insertKV h with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons_of_mem _ h)

theorem insertKV_pairwise {α : Type} (k : GoString) (v : α) : ∀ (l : List (GoString × α)),
    l.Pairwise (fun a b => gsLt a.1 b.1 = true) →
    (insertKV k v l).Pairwise (fun a b => gsLt a.1 b.1 = true)
  | [], _ => by simp [insertKV]
  | (k', v') :: rest, h => by
      rw [List.pairwise_cons] at h
      unfold insertKV
      split
      · rename_i hk; subst hk
        rw [List.pairwise_cons]; exact ⟨h.1, h.2⟩
      · split
        · rename_i hk hlt
          refine List.Pairwise.cons ?_ (List.Pairwise.cons h.1 h.2)
          intro b hb
          rcases List.mem_cons.1 hb with rfl | hb'
          · exact hlt
          · exact gsLt_trans hlt (h.1 b hb')
        · rename_i hk hlt
          have hgt : gsLt k' k = true := by
            cases hc : gsLt k' k with
            | true => rfl
            | false => exact absurd (gsLt_total (by simpa using hlt) hc).symm hk
          refine List.Pairwise.cons ?_ (insertKV_pairwise k v rest h.2)
          intro b hb
          rcases mem_insertKV hb with rfl | hb'
          · exact hgt
          · exact h.1 b hb'

theorem lookupKV_insertKV {α : Type} (k j : GoString) (v : α) : ∀ (l : List (GoString × α)),
    lookupKV j (insertKV k v l) = if k = j then some v else lookupKV j l
  | [] => by simp [insertKV, lookupKV]
  | (k', v') :: rest => by
      unfold insertKV
      split
      · rename_i hk; subst hk
        by_cases hj : k' = j <;> simp [lookupKV, hj]
      · split
        · by_cases hj : k = j <;> simp [lookupKV, hj]
        · rename_i hk _
          have := lookupKV_insertKV k j v rest
          by_cases hj : k' = j
          · subst hj; simp [lookupKV, Ne.symm hk]
          · simp only [lookupKV, hj, ite_false, this]

theorem kvsOf_foldl {α : Type} : ∀ (l acc : List (GoString × α)),
    keysSorted acc = true →
    keysSorted (l.foldl (fun m (kv : GoString × α) => insertKV kv.1 kv.2 m) acc) = true ∧
    (∀ j, (lookupKV j (l.foldl (fun m (kv : GoString × α) => insertKV kv.1 kv.2 m) acc)).isSome =
      ((lookupKV j acc).isSome || (lookupKV j l).isSome)) ∧
    (∀ e ∈ l.foldl (fun m (kv : GoString × α) => insertKV kv.1 kv.2 m) acc, e ∈ acc ∨ e ∈ l)
  | [], acc, h => by simp [lookupKV, h]
  | (k, v) :: l, acc, h => by
      simp only [List.foldl_cons]
      have hs : keysSorted (insertKV k v acc) = true :=
        (keysSorted_iff_pairwise _).2 (insertKV_pairwise k v acc ((keysSorted_iff_pairwise _).1 h))
      obtain ⟨h1, h2, h3⟩ := kvsOf_foldl l (insertKV k v acc) hs
      refine ⟨h1, ?_, ?_⟩
      · intro j
        rw [h2 j, lookupKV_insertKV,
          show lookupKV j ((k, v) :: l) = if k = j then some v else lookupKV j l from rfl]
        by_cases hj : k = j <;> simp [hj]
      · intro e he
        rcases h3 e he with he | he
        · rcases mem_insertKV he with rfl | he
          · exact Or.inr List.mem_cons_self
          · exact Or.inl he
        · exact Or.inr (List.mem_cons_of_mem _ he)

theorem kvsOf_facts {α : Type} (l : List (GoString × α)) :
    keysSorted (kvsOf l) = true ∧ (∀ j, (lookupKV j (kvsOf l)).isSome = (lookupKV j l).isSome) ∧
    (∀ e ∈ kvsOf l, e ∈ l) := by
  obtain ⟨h1, h2, h3⟩ := kvsOf_foldl l [] rfl
  refine ⟨h1, fun j => by rw [kvsOf, h2 j]; simp [lookupKV], fun e he => ?_⟩
  rcases h3 e he with he | he
  · simp at he
  · exact he

end LawProofs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open LawProofs

/-- A separating conjunction of persistent facts, read back at any member. -/
theorem LawProofs.sepL_mem {α : Type} (f : α → IProp GF) [∀ a, Persistent (f a)] :
    ∀ (xs : List α), sepL f xs ⊢ □ ∀ a, ⌜a ∈ xs⌝ -∗ f a
  | [] => by
      iintro _; imodintro; iintro %a %h; simp at h
  | x :: xs => by
      rw [LawProofs.sepL_cons]
      iintro ⟨#Hx, Hr⟩
      ihave #Hr := LawProofs.sepL_mem f xs $$ Hr
      imodintro
      iintro %a %h
      rcases List.mem_cons.1 h with rfl | h
      · iexact Hx
      · iapply Hr; ipureintro; exact h

theorem LawProofs.isIfaceM_of_mem (M : GMap GoString GoInterface) (kvs : List (GoString × UVal)) :
    ∀ (l : List (GoString × UVal)), (∀ e ∈ l, e ∈ kvs) →
    (□ ∀ a, ⌜a ∈ kvs⌝ -∗ ∃ x, ⌜M !! a.1 = some x⌝ ∗ isIface (GF := GF) x a.2) ⊢ isIfaceM M l
  | [], _ => by unfold isIfaceM; iintro _; ipureintro; trivial
  | (k, v) :: l, h => by
      unfold isIfaceM
      iintro #H
      ihave ⟨%x, %hx, #Hx⟩ := H $$ %(k, v) %(h _ List.mem_cons_self)
      iexists x
      isplitr
      · ipureintro; exact hx
      isplitr
      · iexact Hx
      · iapply LawProofs.isIfaceM_of_mem M kvs l (fun e he => h e (List.mem_cons_of_mem _ he))
        iexact H

theorem isIface_ofMap_law_holds : isIface_ofMap.law (GF := GF) := fun m M kvs hnd hk => by
  iintro #Hm Hl
  ihave #Hl := LawProofs.sepL_mem _ kvs $$ Hl
  obtain ⟨hs, hl, hmem⟩ := kvsOf_facts kvs
  rw [UVal.ofMap, isIface.eq_6]
  iexists m, M
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact Hm
  isplitr
  · ipureintro; exact ⟨hs, fun k => by rw [hk k, hl k]⟩
  iapply LawProofs.isIfaceM_of_mem M kvs (kvsOf kvs) hmem
  iexact Hl

theorem LawProofs.isMFL_of_mem (M : GMap GoString GoInterface) (ms : List (GoString × VSet)) :
    ∀ (l : List (GoString × VSet)), (∀ e ∈ l, e ∈ ms) →
    (□ ∀ a, ⌜a ∈ ms⌝ -∗ ∃ i, ⌜M !! a.1 = some i⌝ ∗ isVSet (GF := GF) i a.2) ⊢ isMFL M l
  | [], _ => by unfold isMFL; iintro _; ipureintro; trivial
  | (k, e) :: l, h => by
      unfold isMFL
      iintro #H
      ihave ⟨%i, %hi, #Hi⟩ := H $$ %(k, e) %(h _ List.mem_cons_self)
      iexists i
      isplitr
      · ipureintro; exact hi
      isplitr
      · iexact Hi
      · iapply LawProofs.isMFL_of_mem M ms l (fun e he => h e (List.mem_cons_of_mem _ he))
        iexact H

theorem isMF_intro_law_holds : isMF_intro.law (GF := GF) := fun m M ms hnd hk => by
  iintro #Hm Hl
  ihave #Hl := LawProofs.sepL_mem _ ms $$ Hl
  obtain ⟨hs, hl, hmem⟩ := kvsOf_facts ms
  unfold MF.ofList isMF
  iexists M
  isplitr
  · iexact Hm
  isplitr
  · ipureintro; exact ⟨hs, fun k => by rw [hk k, MF.get, hl k]⟩
  iapply LawProofs.isMFL_of_mem M ms (kvsOf ms) hmem
  iexact Hl

end laws
end smd
end EtcdGrove
end Perennial
