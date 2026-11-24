/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): `Init0`'s lemmas (empty slices holding
empty lists, replicated slices), moved out of its proof file so that other proofs import them
from a defs module (import tiers); names and statements unchanged.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Init0_set {α : Type} (a z : α) (n k : Nat) (hk : k < n) :
    (List.replicate k a ++ List.replicate (n - k) z).set k a =
      List.replicate (k + 1) a ++ List.replicate (n - (k + 1)) z := by
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
  rw [hm, show n - (k + 1) = m by omega, List.set_append_right _ _ (by simp), List.length_replicate,
    Nat.sub_self, List.replicate_succ, List.set_cons_zero, List.replicate_succ', List.append_assoc]
  rfl

theorem Init0_rep {A B : Type} (Φ : A → B → IProp GF) [∀ a b, Persistent (Φ a b)] (a : A) (b : B) :
    ∀ N : Nat, Φ a b ⊢ [∗list] x;y ∈ List.replicate N a;List.replicate N b, Φ x y
  | 0 => by simp only [List.replicate_zero]; exact BigSepL2.bigSepL2_nil_affine
  | N + 1 => by
    iintro #H
    simp only [List.replicate_succ]
    iapply BigSepL2.bigSepL2_cons.2
    isplit
    · iexact H
    iapply Init0_rep Φ a b N
    iexact H

theorem Init0_rel {A B : Type} (R : A → B → Prop) (a : A) (b : B) (h : R a b) :
    ∀ N : Nat, List.Forall₂ R (List.replicate N a) (List.replicate N b)
  | 0 => .nil
  | N + 1 => .cons h (Init0_rel R a b h N)

theorem Init0_ints (sl : GoSlice) (N : Nat) (w : w64) (x : Int) (h : sint.Z w = x) :
    sl ↦*□ List.replicate N w ⊢ intsRO (GF := GF) sl (List.replicate N x) := by
  iintro #H
  iunfold intsRO
  iexists _
  isplit
  · iexact H
  ipureintro; simp [List.map_replicate, h]

theorem Init0_strsNil : ⊢ strsRO (GF := GF) slice.nil [] := by
  iunfold strsRO; iapply ownSlice_nil

theorem Init0_logNil : ⊢ logRO (GF := GF) slice.nil [] := by
  iunfold logRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_msgsNil : ⊢ msgsRO (GF := GF) slice.nil [] := by
  iunfold msgsRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_qitemsNil : ⊢ qitemsRO (GF := GF) slice.nil [] := by
  iunfold qitemsRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_readRecsNil : ⊢ readRecsRO (GF := GF) slice.nil [] := by
  iunfold readRecsRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_factsNil : ⊢ factsRO (GF := GF) slice.nil [] := by
  iunfold factsRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_votesNil : ⊢ votesRO (GF := GF) slice.nil [] := by
  iunfold votesRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_leadersNil : ⊢ leadersRO (GF := GF) slice.nil [] := by
  iunfold leadersRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_termLogsNil : ⊢ termLogsRO (GF := GF) slice.nil [] := by
  iunfold termLogsRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_termConfsNil : ⊢ termConfsRO (GF := GF) slice.nil [] := by
  iunfold termConfsRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_termIntsNil : ⊢ termIntsRO (GF := GF) slice.nil [] := by
  iunfold termIntsRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_preNone : ⊢ preRO (GF := GF) (zero_val Loc) none := by
  unfold preRO; ipureintro; rfl

end proof

end AntCheck
end EtcdGrove
end Perennial
