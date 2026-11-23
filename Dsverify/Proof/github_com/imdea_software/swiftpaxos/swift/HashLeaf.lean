/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HashLeaf.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`swift/dpath.go`'s hashing functions (internal specs with their proofs): `putId` (the id's 8
bytes, `sp.encCmdId`), `hashStart` (a path's first round), `hash` (a next round),
`HashLog.chain` (either), over `crypto/sha256.Sum256`'s spec (a hypothesis).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ChainHash
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Marshal
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.swift
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLeafDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- One store `bs[i] = x` into the buffer `Hsl` (the bounds check first). -/
local macro "store8" : tactic => `(tactic| (
  (try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)])
  wp_pures
  wp_apply wp_store_slice_index _ _ _ _ $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro
    simp only [List.length_set, List.length_append, Hold]
    word
  (try wp_auto)))

theorem putId.wp_proof : putId.spec := by
  intro bs old rest x
  wp_start as ⟨Hsl, %Hold⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_append, Hold] at Hlen
  wp_auto
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  iapply HΦ
  rw [set8_app _ _ Hold, le32x2_sbytes]
  simp only [sp.encCmdId, toCmdId]
  iexact Hsl

theorem hashStart.wp_proof (wp_putId : putId.spec)
    (wp_Sum256 : crypto.sha256.Sum256.spec (GF := netDistGF) (hG := hG)) :
    hashStart.spec := by
  intro x
  wp_start
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply wp_putId sl (List.replicate 8 (zero_val w8)) [] x $$ [Hsl] as Hsl
  · rw [List.append_nil]; iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_Sum256 sl _ (DFrac.own 1) $$ [$Hpkg $Hsl] as %h ⟨-, Hh⟩
  try wp_auto
  iapply HΦ
  rw [List.append_nil] at *
  iapply sp.hashOf_of_is_hash $$ Hh

theorem hash.wp_proof (wp_putId : putId.spec)
    (wp_Sum256 : crypto.sha256.Sum256.spec (GF := netDistGF) (hG := hG)) :
    hash.spec := by
  intro initial x
  wp_start as %Hil
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_replicate] at Hlen
  wp_pures
  rename_i gi
  irename: (gi ↦ zero_val w64) => Hgi
  ihave HL : (∃ (k : w64) (ik : w64) (bk : w8),
      "i" ∷ i_ptr ↦ k ∗ "b" ∷ b_ptr ↦ bk ∗ "Hgi" ∷ gi ↦ ik ∗
      "Hsl" ∷ sl ↦* (initial.arr.take (sint.nat k) ++ List.replicate (40 - sint.nat k) (W8 0)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 32⌝ : IProp netDistGF) $$ [i b Hgi Hsl]
  · iexists (W64 0), _, _; iframe i b Hgi
    isplitl [Hsl]
    · iExactEq Hsl; simp; rfl
    ipureintro; decide
  wp_for HL
  wp_if_destruct
  · have hk32 : sint.Z k < 32 := by
      have h := Hif; simp at h; have : sint.Z (W64 32) = 32 := rfl; omega
    have hkn : sint.nat k < initial.arr.length := by rw [Hil]; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hk.1), List.getElem?_eq_getElem hkn]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk.1, by word⟩)]
    wp_pures
    wp_apply wp_store_slice_index _ _ _ _ $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; simp [Hil]; word
    wp_for_post
    iframe
    iexists (k + W64 1), k, _
    iframe
    isplitl [Hsl]
    · iExactEq Hsl
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      rw [hk1, (by word : (sint.Z k).toNat = sint.nat k), set_take_rep _ _ _ hkn 40 (by word)]
    ipureintro; word
  · have hk32 : sint.Z k = 32 := by
      have h := Hif; simp at h; have : sint.Z (W64 32) = 32 := rfl; omega
    have hk : sint.nat k = 32 := by word
    rw [hk, List.take_of_length_le (by omega)] at *
    wp_pures
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word, Hwf.2⟩)]
    rw [show 40 - 32 = 8 from rfl] at *
    ihave ⟨H1, H2⟩ := (ownSlice_split_all (W64 32) sl (DFrac.own 1) _ ⟨by decide, by word⟩).1 $$ Hsl
    have h32 : sint.nat (W64 32) = initial.arr.length := by rw [Hil]; rfl
    rw [h32, List.take_left, List.drop_left] at *
    try wp_auto
    wp_apply wp_putId (slice.slice sl w8 (W64 32) sl.len) (List.replicate 8 (W8 0)) [] x
      $$ [H2] as H2
    · rw [List.append_nil]; iframe H2; ipureintro; rfl
    rw [List.append_nil]
    ihave Hsl := ownSlice_combine (W64 32) sl (DFrac.own 1) _ _ (W64 0) sl.len
      ⟨by rw [Hil]; rfl, by decide, by decide, by word⟩ $$ H1 H2
    ihave Hsl := ownSlice_trivial_slice_2 _ _ _ $$ Hsl
    try wp_auto
    wp_apply wp_Sum256 sl _ (DFrac.own 1) $$ [$Hpkg $Hsl] as %h ⟨-, Hh⟩
    try wp_auto
    iapply HΦ
    iapply sp.hashOf_of_is_hash $$ Hh

theorem HashLog.chain.wp_proof (wp_hash : hash.spec) (wp_hashStart : hashStart.spec) :
    HashLog.chain.spec := by
  intro l h started x
  wp_start as %Hl
  wp_auto
  cases started
  · wp_auto
    wp_apply wp_hashStart x $$ [$Hpkg] as %h' Hh
    try wp_auto
    iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]; iexact Hh
  · wp_auto
    wp_apply wp_hash h x $$ [$Hpkg] as %h' Hh
    · ipureintro; exact Hl
    try wp_auto
    iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]; iexact Hh

end proofs

end swift

end Perennial.github_com.imdea_software.swiftpaxos
