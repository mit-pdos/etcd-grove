-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/EntrySize.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/EntrySize.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`, "Stage 3a"). Each set field adds its tag and its
value's size (`wp_sizeVarint`, `SizeVarint.lean`: the loop is `varintSize`), the unknown fields their
length (read from the frozen hidden fields, `pbMsg_uf`); the running sum is kept as the word of the
model's partial sum (`W64 s`), so it agrees with `entrySize c` whenever that is below `2^63`.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.raftpb.SizeVarint
public import KvNet.Proof.go_etcd_io.raft.v3.raftpb.CloneLeaf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The size of an `Entry`'s `data` field (`entrySize`'s fourth summand). -/
private def dataSize (d : Option (List w8)) : Nat :=
  match d with | none => 0 | some bs => 1 + varintSize bs.length + bs.length

/-- A frozen `bytes` field's slice is `nil` exactly when the field is unset. -/
private theorem bytesC_nil (ds : GoSlice) (o : Option (List w8)) :
    bytesC (GF := GF) ds o ⊢ ⌜ds = slice.nil ↔ o = none⌝ := by
  cases o with
  | none => simp only [bytesC]; iintro %H; ipureintro; simp [H]
  | some bs => simp only [bytesC]; iintro ⟨%H, -⟩; ipureintro; simp [H]

theorem raftpb.EntrySize.wp_proof : raftpb.EntrySize.spec (GF := GF) (hG := hG) := by
  intro l c
  wp_start as #He
  iunfold entRoC at He
  icases He with ⟨%pt, %pi, %pty, %ds, %Hnn, #HT, #cT, #HI, #cI, #HY, #cY, #HD, #Hd, #Hpb⟩
  icases pbMsg_uf _ _ _ $$ Hpb with ⟨%us, #Hus, #Hub⟩
  ihave %Hul := ownSlice_len _ _ _ $$ Hub
  ihave %Hpty := optCell_null _ _ $$ cY
  ihave %Hpt := optCell_null _ _ $$ cT
  ihave %Hpi := optCell_null _ _ $$ cI
  ihave %Hds := bytesC_nil _ _ $$ Hd
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_join iprop(e_ptr ↦ l ∗
      n_ptr ↦ W64 (optVarintSize (c.type.map fun t => (uint.Z (W64 (sint.Z t))).toNat) : Int))
    with [e n] as ⟨e, n⟩
  · rw [Hpty.1 rfl]
    simp only [Option.map_none, optVarintSize, Int.natCast_zero]
    iframe
  · obtain ⟨t, ht⟩ : ∃ t, c.type = some t := by
      cases h : c.type with
      | none => exact absurd (Hpty.2 h) (by assumption)
      | some t => exact ⟨t, rfl⟩
    have e : optCell (GF := GF) pty c.type = iprop(pty ↦□ t) := by rw [ht]; rfl
    ihave #Ht : (pty ↦□ t : IProp GF) $$ []
    · rw [← e]; iexact cY
    wp_auto
    wp_apply wp_sizeVarint as %k %Hk
    have h10 := varintSize_le_10 (uint.Z (W64 (sint.Z t))).toNat (by word)
    have hk : W64 0 + (W64 1 + k) =
        W64 (optVarintSize (c.type.map fun t => (uint.Z (W64 (sint.Z t))).toNat) : Int) := by
      rw [ht]; simp only [Option.map_some, optVarintSize]; push_cast; word
    rw [hk]
    wp_join_done
  generalize hsT : optVarintSize (c.type.map fun t => (uint.Z (W64 (sint.Z t))).toNat) = sT
  wp_join iprop(e_ptr ↦ l ∗ n_ptr ↦ (W64 (sT : Int) + W64 (optVarintSize (c.term.map fun v => (uint.Z v).toNat) : Int)))
    with [e n] as ⟨e, n⟩
  · rw [Hpt.1 rfl]
    simp only [Option.map_none, optVarintSize, Int.natCast_zero]
    rw [show W64 (sT : Int) + W64 0 = W64 (sT : Int) by word]
    iframe
  · obtain ⟨v, hv⟩ : ∃ v, c.term = some v := by
      cases h : c.term with
      | none => exact absurd (Hpt.2 h) (by assumption)
      | some v => exact ⟨v, rfl⟩
    have e : optCell (GF := GF) pt c.term = iprop(pt ↦□ v) := by rw [hv]; rfl
    ihave #Hv : (pt ↦□ v : IProp GF) $$ []
    · rw [← e]; iexact cT
    wp_auto
    wp_apply wp_sizeVarint as %k %Hk
    have h10 := varintSize_le_10 (uint.Z v).toNat (by word)
    have hk : W64 (sT : Int) + (W64 1 + k) =
        W64 (sT : Int) + W64 (optVarintSize (c.term.map fun v => (uint.Z v).toNat) : Int) := by
      rw [hv]; simp only [Option.map_some, optVarintSize]; push_cast; word
    rw [hk]
    wp_join_done
  generalize hsTe : optVarintSize (c.term.map fun v => (uint.Z v).toNat) = sTe
  wp_join iprop(e_ptr ↦ l ∗ n_ptr ↦ ((W64 (sT : Int) + W64 (sTe : Int)) + W64 (optVarintSize (c.index.map fun v => (uint.Z v).toNat) : Int)))
    with [e n] as ⟨e, n⟩
  · rw [Hpi.1 rfl]
    simp only [Option.map_none, optVarintSize, Int.natCast_zero]
    rw [show (W64 (sT : Int) + W64 (sTe : Int)) + W64 0 = (W64 (sT : Int) + W64 (sTe : Int)) by word]
    iframe
  · obtain ⟨v, hv⟩ : ∃ v, c.index = some v := by
      cases h : c.index with
      | none => exact absurd (Hpi.2 h) (by assumption)
      | some v => exact ⟨v, rfl⟩
    have e : optCell (GF := GF) pi c.index = iprop(pi ↦□ v) := by rw [hv]; rfl
    ihave #Hv : (pi ↦□ v : IProp GF) $$ []
    · rw [← e]; iexact cI
    wp_auto
    wp_apply wp_sizeVarint as %k %Hk
    have h10 := varintSize_le_10 (uint.Z v).toNat (by word)
    have hk : (W64 (sT : Int) + W64 (sTe : Int)) + (W64 1 + k) =
        (W64 (sT : Int) + W64 (sTe : Int)) + W64 (optVarintSize (c.index.map fun v => (uint.Z v).toNat) : Int) := by
      rw [hv]; simp only [Option.map_some, optVarintSize]; push_cast; word
    rw [hk]
    wp_join_done
  generalize hsI : optVarintSize (c.index.map fun v => (uint.Z v).toNat) = sI
  wp_join iprop(e_ptr ↦ l ∗ n_ptr ↦ ((W64 (sT : Int) + W64 (sTe : Int) + W64 (sI : Int)) + W64 ((dataSize c.data) : Int)))
    with [e n] as ⟨e, n⟩
  · rw [Hds.1 rfl]
    simp only [dataSize, Int.natCast_zero]
    rw [show (W64 (sT : Int) + W64 (sTe : Int) + W64 (sI : Int)) + W64 0 = (W64 (sT : Int) + W64 (sTe : Int) + W64 (sI : Int)) by word]
    iframe
  · obtain ⟨bs, hbs⟩ : ∃ bs, c.data = some bs := by
      cases h : c.data with
      | none => exact absurd (Hds.2 h) (by assumption)
      | some bs => exact ⟨bs, rfl⟩
    have e : bytesC (GF := GF) ds c.data = iprop(⌜ds ≠ slice.nil⌝ ∗ ds ↦*□ bs) := by rw [hbs]; rfl
    ihave #Hd' : iprop(⌜ds ≠ slice.nil⌝ ∗ ds ↦*□ bs) $$ []
    · rw [← e]; iexact Hd
    icases Hd' with ⟨-, #Hbs⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hbs
    wp_apply wp_sizeVarint as %k %Hk
    have h10 := varintSize_le_10 (uint.Z ds.len).toNat (by word)
    have hk : (W64 (sT : Int) + W64 (sTe : Int) + W64 (sI : Int)) + (W64 1 + k + ds.len) = (W64 (sT : Int) + W64 (sTe : Int) + W64 (sI : Int)) + W64 ((dataSize c.data) : Int) := by
      rw [hbs]
      have hu : (uint.Z ds.len).toNat = bs.length := by
        have h1 := Hbl.1; have h2 := Hbl.2; word
      rw [hu] at Hk
      simp only [dataSize]
      push_cast
      word
    rw [hk]
    wp_join_done
  generalize hsD : (dataSize c.data) = sD
  iapply HΦ
  ipureintro
  intro hlt
  have hE : (entrySize c : Int) = sT + sTe + sI + sD + c.uf.length := by
    rw [← hsT, ← hsTe, ← hsI, ← hsD]; rfl
  have hw : (W64 (sT : Int) + W64 (sTe : Int) + W64 (sI : Int)) + W64 (sD : Int) + us.len = W64 (entrySize c : Int) := by
    rw [hE]
    have : (c.uf.length : Int) = sint.Z us.len := by
      have h1 := Hul.1; have h2 := Hul.2; word
    word
  rw [hw]
  word

end proof

end EtcdGrove
end Perennial
