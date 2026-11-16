/- Lean-first (no Rocq counterpart). The proof of `toRaft`: the cells (`newU64`, `EntryType.Enum`)
and the data (`entData`), the struct split into its fields, everything frozen and the hidden fields
made into raft's `protobuf` invariant (`pbMsg_alloc`); the size bound (`absEnt_small`). -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.toRaft
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.newU64
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.entData
public import Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.entData

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

theorem tEntData_length (e : TEnt) : (tEntData e).length = uint.nat e.size' := by
  rw [tEntData_eq]; simp; omega

theorem tEntData_ne_nil (e : TEnt) (h : 0 < uint.nat e.size') : tEntData e ≠ [] := by
  intro h0
  have := tEntData_length e
  rw [h0] at this
  simp at this; omega

theorem optVarintSize_w64 (v : Nat) (h : v < 2 ^ 64) : optVarintSize (some v) ≤ 11 := by
  have := varintEnc_length_w64 v h
  simp only [optVarintSize, varintSize]; omega

/-- **`toRaft`'s entry is below Go's allocation limit.** -/
theorem absEnt_small (e : TEnt) (h0 : 0 < uint.nat e.size') (h : uint.nat e.size' < 2 ^ 40) :
    walEntSmall (absEnt e) := by
  unfold walEntSmall walEntCanon entrySize
  have hne := tEntData_ne_nil e h0
  have hl := tEntData_length e
  simp only [absEnt, hne, ↓reduceIte, Option.map_some]
  have h1 := optVarintSize_w64 (uint.Z (W64 (sint.Z (W32 0)))).toNat (by word)
  have h2 := optVarintSize_w64 (uint.Z e.term').toNat (by word)
  have h3 := optVarintSize_w64 (uint.Z e.index').toNat (by word)
  have h4 := varintEnc_length_w64 (tEntData e).length (by omega)
  unfold varintSize
  simp only [List.length_nil]
  omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem toRaft.wp_proof (wp_newU64 : newU64.spec (GF := GF) (hG := hG))
    (wp_entData : entData.spec (GF := GF) (hG := hG))
    (wp_Enum : raftpb.EntryType.Enum.spec (GF := GF) (hG := hG)) :
    toRaft.spec (GF := GF) (hG := hG) := by
  intro e h0 hsz
  wp_start
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_newU64 as %pi Hpi
  try wp_auto
  wp_apply wp_newU64 as %pt Hpt
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  try wp_auto
  wp_apply wp_Enum $$ [$Hpb] as %pty Hpty
  try wp_auto
  iapply wp_fupd
  wp_apply wp_entData e (by omega) as %ds ⟨Hds, -⟩
  try wp_auto
  ihave %Hnn := typedPointsto_not_null $$ «$r0»
  ihave %Hlen := ownSlice_len $$ Hds
  icases typedPointsto_split _ _ _ $$ «$r0» with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨Hst, HT, HI, HY, HD, Huf, Hsc, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HY with #HY
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HD with #HD
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hpt with #Hpt
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hpi with #Hpi
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hpty with #Hpty
  imod ownSlice_persist $$ Hds with #Hds
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod (pbMsg_alloc raftpb.Entry «$r0_ptr» _ _ _ [] ⊤ (ufWire_nil _)) $$ [Hst Hsc Huf Hnil] with #Hpbm
  · iframe
  imodintro
  iapply HΦ
  simp only [walRaftP]
  unfold walEntIn entRoC
  have hne := tEntData_ne_nil e h0
  have hds : ds ≠ slice.nil := by
    intro hd; subst hd
    rw [tEntData_length] at Hlen
    simp [slice.nil] at Hlen; word
  simp only [walEntCanon, absEnt, hne, ↓reduceIte]
  isplitl
  · iexists pt, pi, pty, ds
    iframe HT HI HY HD Hpbm
    simp only [optCell, bytesC]
    iframe Hpt Hpi Hpty Hds
    ipureintro; exact ⟨Hnn, hds⟩
  · ipureintro; exact absEnt_small e h0 hsz

end proof

end etcd_wal
end EtcdGrove
end Perennial
