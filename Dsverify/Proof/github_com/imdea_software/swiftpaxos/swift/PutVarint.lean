/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/PutVarint.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`putUvarint`/`putVarint` (swift/varint.go, copies of Go's `encoding/binary` PutUvarint/PutVarint;
fork change P1, notes/prove-swift.md §13): the varint of `x` at the buffer's front.

* `swift.wp_putUvarint`: `putUvarint(buf, n)` for any `n < 2^64` whose varint (`sp.uvarint n`)
  fits in the buffer;
* `swift.PutVarint.wp_proof`: the swift messages' writers' hypothesis `swift.PutVarint.specH`
  (Proof/swift/MarshalSpecs.lean): `putVarint(buf, x)` for a length `0 ≤ x < 2^62`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.VarintPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PutVarintDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

set_option goose.wp.extras true

theorem swift.PutVarint.wp_proof : swift.PutVarint.specH (hG := hG) := by
  intro s bs x
  wp_start as ⟨Hs, %Hx⟩
  obtain ⟨h10, hx0, hx62⟩ := Hx
  have hn : (sint.nat x : Int) = sint.Z x := Int.toNat_of_nonneg hx0
  have hux : (x <<< W64 1 : w64) = W64 ((2 * sint.nat x : Nat) : Int) := by
    simp only [sint.Z] at hx0 hx62 hn
    have hxn : (x.toNat : Int) = x.toInt := by
      have := BitVec.toInt_eq_toNat_cond x; split at this <;> omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
    simp only [W64, BitVec.toNat_ofInt]
    rw [show ((1 : Int) % ((2 ^ 64 : Nat) : Int)).toNat = 1 from rfl, Nat.shiftLeft_eq]
    omega
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z x < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
  wp_auto
  rw [hux]
  wp_apply swift.wp_putUvarint s bs (2 * sint.nat x) $$ [$Hs] as %r ⟨%Hr, Hs⟩
  · ipureintro
    refine ⟨by omega, ?_⟩
    have := sp.uvarint_length (2 * sint.nat x) 10 (by decide) (by omega)
    omega
  iapply HΦ
  unfold sp.varintLen
  iframe Hs
  ipureintro; exact Hr

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
