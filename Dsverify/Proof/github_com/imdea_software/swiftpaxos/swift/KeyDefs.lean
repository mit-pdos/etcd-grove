/-
The definitions, specs and lemmas of `Key.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.KeySpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.lki
open swift.hlog (cmdIdDecEq cmdId_intoValInj)

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

set_option goose.wp.extras true

theorem dropIf_cons (x y : swift.CommandId) (L : List swift.CommandId) :
    dropIf x (y :: L) = if y = x then [] else y :: L := by
  unfold dropIf; simp

theorem dropIf_cons_eq (x y : swift.CommandId) (L : List swift.CommandId) (h : y = x) :
    dropIf x (y :: L) = [] := by
  subst h; unfold dropIf; simp

theorem dropIf_cons_ne (x y : swift.CommandId) (L : List swift.CommandId) (h : y ≠ x) :
    dropIf x (y :: L) = y :: L := by
  unfold dropIf; simp [h]

theorem dropIf_nil (x : swift.CommandId) : dropIf x [] = [] := rfl

set_option hygiene false in
/-- The guard `y == x` on command ids, as goose compiles it (field by field): the case split
gives `y = x` or `y ≠ x`. -/
local macro "cmd_guard" t1:tacticSeq "|" t2:tacticSeq : tactic => `(tactic| (
  wp_if_destruct
  · try wp_auto
    wp_if_destruct
    · have hyx : y = x := by (cases y; cases x; simp_all)
      ($t1)
    · have hyx : y ≠ x := by (intro h; subst h; simp_all)
      try wp_auto
      ($t2)
  · have hyx : y ≠ x := by (intro h; subst h; simp_all)
    try wp_auto
    ($t2)))

set_option hygiene false in
/-- `remove`'s second statement (on `lastWrite`), once `lastCmd` holds `LC ↦*□ dropIf x C`. -/
local macro "second_block" : tactic => `(tactic| (
  try wp_auto
  wp_if_destruct
  · obtain ⟨y, W', rfl⟩ : ∃ y W', W = y :: W' := by
      cases W with
      | nil => simp at Hlwl; omega
      | cons y W' => exact ⟨y, W', rfl⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by omega⟩)]
    wp_apply wp_load_slice_index _ _ _ _ y (by decide) $$ [Hlw] as -
    · iframe Hlw; ipureintro; rfl
    try wp_auto
    cmd_guard
      (wp_apply wp_slice_literal (V := swift.CommandId) []
       isplitr
       · ipureintro; rfl
       iintro %s2 ⟨Hs2, -⟩
       ipersist Hs2
       try wp_auto
       iapply HΦ
       iexists _, _
       iframe Hki HC
       rw [dropIf_cons_eq _ _ _ hyx]
       iexact Hs2) |
      (iapply HΦ
       iexists _, _
       iframe Hki HC
       rw [dropIf_cons_ne _ _ _ hyx]
       iexact Hlw)
  · try wp_auto
    obtain rfl : W = [] := by
      cases W with
      | nil => rfl
      | cons y W' => simp at Hlwl; omega
    iapply HΦ
    iexists _, _
    iframe Hki HC
    rw [dropIf_nil]
    iexact Hlw))

end proofs


end swift.lki

end Perennial.github_com.imdea_software.swiftpaxos
