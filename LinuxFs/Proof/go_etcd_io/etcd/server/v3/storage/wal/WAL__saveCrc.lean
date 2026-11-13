/-
The proof of `WAL.saveCrc.spec` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/encoder__encodeG.lean`):
`encode(&Record{Type: CrcType, Crc: &prevCrc})` over the guarded `encode` (`encoder.encode.specG`).
W6 of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeG

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

/-- A varint is at most one byte per unit (`raft`'s `varintSize_le_succ`, which the part cannot
import). -/
theorem wal_varintSize_le_succ : ∀ n : Nat, varintSize n ≤ n + 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold varintSize
    rw [varintEnc]
    split
    · simp
    · simp only [List.length_cons]
      have := ih (n / 128) (by omega)
      unfold varintSize at this
      omega

/-- A CRC record (no data) is small. -/
theorem recSize_crc (k : w32) : recSize (recOf ⟨crcType, k, []⟩) < 2 ^ 47 := by
  have h1 := wal_varintSize_le_succ (uint.nat crcType)
  have h2 := wal_varintSize_le_succ (uint.nat k)
  have h3 : uint.nat crcType < 2 ^ 8 := by decide
  have h4 : uint.nat k < 2 ^ 32 := by unfold uint.nat; exact BitVec.isLt _
  simp only [recSize, recOf, and_true, ite_true, List.length_nil, Nat.add_zero]
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.saveCrc.wp_proof
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specG (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.saveCrc.spec (GF := GF) (hG := hG) := by
  intro w e wi W B ok out pend c prev hpc hok
  iintro #Hw
  wp_start as ⟨#Henv, Hwe, He, Hout⟩
  unfold go_etcd_io.etcd.server.v3.storage.wal.CrcType
  try wp_auto
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ «$v0» with #Ht
  ihave #Henc := wp_encode e wi W B ok out pend c «$a0_ptr» crcType [] (recSize_crc _) hpc hok $$ Hw
  wp_apply Henc $$ [He Hout «$a0»] as %err ⟨%pend', He, -, Hr⟩
  · iframe Henv He Hout
    iunfold encRecIn
    iexists _
    iframe «$a0»
    have hd : (recOf ⟨crcType, 0#32, []⟩).data = none := by simp [recOf]
    simp only [hd, recBytes]
    rw [show crcType = W64 4 from rfl]
    isplitl
    · iexact Ht
    ipureintro; simp
  try wp_auto
  iapply HΦ
  iexists pend'
  iframe Hwe He Hr

end proof

end EtcdGrove
end Perennial
