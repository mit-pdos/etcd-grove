/-
The pure lemmas of `toRaft.lean`'s proof (`tEntData_length`, `absEnt_small`, ...), in a module of
their own so that `SavePure.lean` imports them without the proof (import tiers, 2026-11-18).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.toRaft
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.newU64
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.entData
public import Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.entDataLemmas

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

end proof

end etcd_wal
end EtcdGrove
end Perennial
