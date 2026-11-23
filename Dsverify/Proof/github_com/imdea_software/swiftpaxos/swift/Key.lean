/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Key.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`lightKeyInfo`'s proofs (swift/key.go): `newLightKeyInfo`, `add`, `remove`,
`getConflictCmds` against the specs of `KeySpecs.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.KeySpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.KeyDefs

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

theorem newLightKeyInfo.wp_proof : newLightKeyInfo.spec := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := swift.CommandId) []
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨Hs1, -⟩
  try wp_auto
  wp_apply wp_slice_literal (V := swift.CommandId) []
  isplitr
  · ipureintro; rfl
  iintro %s2 ⟨Hs2, -⟩
  ipersist Hs1
  ipersist Hs2
  try wp_auto
  iapply HΦ
  unfold lkiOwn
  iexists _, _
  iframe «$r0» Hs1 Hs2

theorem lightKeyInfo.add.wp_proof : lightKeyInfo.add.spec := by
  intro ki W C c x
  wp_start as ⟨Hown, %Hlen⟩
  unfold lkiOwn
  icases Hown with ⟨%lw, %lc, Hki, #Hlw, #Hlc⟩
  ihave %Hlcl := ownSlice_len _ _ _ $$ Hlc
  wp_auto
  wp_if_destruct
  · -- a put
    wp_apply wp_slice_literal (V := swift.CommandId) [x]
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨Hs1, -⟩
    ipersist Hs1
    try wp_auto
    wp_apply wp_slice_literal (V := swift.CommandId) [x]
    isplitr
    · ipureintro; rfl
    iintro %s2 ⟨Hs2, -⟩
    ipersist Hs2
    try wp_auto
    iapply HΦ
    iexists _, _
    iframe Hki
    unfold addTo; rw [if_pos Hif]
    iframe Hs1 Hs2
  · have hle : 0 ≤ sint.Z lc.len ∧ sint.Z lc.len ≤ sint.Z (lc.len + W64 1) := by
      constructor
      · omega
      · have e1 : sint.nat lc.len = (sint.Z lc.len).toNat := rfl
        word
    iapply wp_fupd
    wp_apply (wp_slice_make3 (V := swift.CommandId) lc.len (lc.len + W64 1) hle) as %ls ⟨Hls, Hcap, %Hcapeq⟩
    try wp_auto
    wp_apply (wp_slice_copy (V := swift.CommandId)) $$ [$Hls $Hlc] as %n ⟨%Hn, Hls, -⟩
    try wp_auto
    wp_apply wp_slice_literal (V := swift.CommandId) [x]
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨Hs1, -⟩
    try wp_auto
    wp_apply (wp_slice_append (V := swift.CommandId)) $$ [$Hls $Hcap $Hs1] as %s' ⟨Hs', -, -⟩
    ipersist Hs'
    iapply HΦ
    iexists _, _
    iframe Hki
    unfold addTo; rw [ite_eq_right_iff.mpr (fun h => absurd h Hif)]
    iframe Hlw
    have hl : sint.nat lc.len = C.length := by omega
    simp only [List.length_replicate, hl, List.take_length, List.drop_eq_nil_of_le (Nat.le_of_eq (List.length_replicate ..)), List.append_nil]
    imodintro; iexact Hs'

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

set_option hygiene false in
theorem lightKeyInfo.remove.wp_proof : lightKeyInfo.remove.spec := by
  intro ki W C c x
  wp_start as Hown
  unfold lkiOwn
  icases Hown with ⟨%lw, %lc, Hki, #Hlw, #Hlc⟩
  ihave %Hlcl := ownSlice_len _ _ _ $$ Hlc
  ihave %Hlwl := ownSlice_len _ _ _ $$ Hlw
  have e0 : sint.Z (W64 0) = 0 := rfl
  have e1 : sint.nat lc.len = (sint.Z lc.len).toNat := rfl
  have e2 : sint.nat lw.len = (sint.Z lw.len).toNat := rfl
  wp_auto
  wp_if_destruct
  · obtain ⟨y, C', rfl⟩ : ∃ y C', C = y :: C' := by
      cases C with
      | nil => simp at Hlcl; omega
      | cons y C' => exact ⟨y, C', rfl⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by omega⟩)]
    wp_apply wp_load_slice_index _ _ _ _ y (by decide) $$ [Hlc] as -
    · iframe Hlc; ipureintro; rfl
    try wp_auto
    cmd_guard
      (wp_apply wp_slice_literal (V := swift.CommandId) []
       isplitr
       · ipureintro; rfl
       iintro %s1 ⟨Hs1, -⟩
       ipersist Hs1
       ihave #HC : (_ ↦*□ dropIf x (y :: C') : IProp netDistGF) $$ [Hs1]
       · rw [dropIf_cons_eq _ _ _ hyx]; iexact Hs1
       clear hyx
       second_block) |
      (ihave #HC : (lc ↦*□ dropIf x (y :: C') : IProp netDistGF) $$ [Hlc]
       · rw [dropIf_cons_ne _ _ _ hyx]; iexact Hlc
       clear hyx
       second_block)
  · obtain rfl : C = [] := by
      cases C with
      | nil => rfl
      | cons y W' => simp at Hlcl; omega
    ihave #HC : (lc ↦*□ dropIf x [] : IProp netDistGF) $$ [Hlc]
    · rw [dropIf_nil]; iexact Hlc
    second_block

theorem lightKeyInfo.getConflictCmds.wp_proof : lightKeyInfo.getConflictCmds.spec := by
  intro ki W C c
  wp_start as Hown
  unfold lkiOwn
  icases Hown with ⟨%lw, %lc, Hki, #Hlw, #Hlc⟩
  wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hif)]
    iframe Hlw
    iexists _
    iframe
    all_goals first | iexact Hlc | iexact Hlw
  · try wp_auto
    iapply HΦ
    rw [ite_eq_right_iff.mpr (fun h => absurd h Hif)]
    iframe Hlc
    iexists _
    iframe
    all_goals first | iexact Hlc | iexact Hlw

end proofs


end swift.lki

end Perennial.github_com.imdea_software.swiftpaxos
