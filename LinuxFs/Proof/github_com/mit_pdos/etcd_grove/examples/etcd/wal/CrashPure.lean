/-
Lean-first (no Rocq counterpart).

# The tester's relation across a crash (pure; WAL W4c step 2, W4c U1)

The part `LinuxFs/`'s copy of the pure section of the main tree's `Crash.lean` (W4c U1, 2026-11-14,
`notes/wal-fsext-w4c-plan.md`): the accounting of a candidate (`tCandOk`, `tPreOk`) survives the
abstract crash of the WAL state (`absDisk_semantics.crash`, which the `fsExt` WAL's `walStCrash` is,
`wal/Ghost.lean`). The crash obligation itself (`tester_crash`, over `absDiskExt`'s and
`durableExt`'s crash lemmas) is U5's, over `walInv_crash`/`walBootCrash` and `lib/durable`'s crash.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The relation across a crash (pure) -/

section pure
variable [GooseExts]

/-- **The accounting survives the crash**: the crashed state (an image `I` of `d.H` at the
candidate's mark, `unl` and `pur` clamped, the read position `k ≤ min pur |I|`) is accounted for by
the same candidate. -/
theorem tCandOk_crash {o : TOracle} {c : TCand} {d : WalDur} {I : List (WalOpG WalEnt)} {k : Nat}
    (hc : tCandOk o c d) (hI : walImg d.H (tCandMark o c) I) (hk : k ≤ min d.pur I.length) :
    tCandOk o c { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } := by
  obtain ⟨himg, hpur, -, hunl, hsz, hwf⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, hsz, hwf⟩
  · exact walImg_trans himg (walImg_map WalOpG.toM WalEnt.toM (fun _ _ => rfl) hI)
  · exact Nat.le_trans (Nat.min_le_left _ _) hpur
  · exact Nat.le_trans (Nat.le_trans hk (Nat.min_le_left _ _)) hpur
  · exact Nat.le_trans (Nat.min_le_left _ _) hunl

/-- **`Create`'s fresh WAL survives the crash** (or vanishes): its crash image is empty, and the
clamped positions stay 0. -/
theorem tPreOk_crash {o : TOracle} {d : WalDur} {I : List (WalOpG WalEnt)} {k : Nat}
    (hd : d.H = [] ∧ d.unl = 0 ∧ d.pur = 0 ∧ d.cut = 0 ∧ d.sized = true)
    (hI : walImg d.H 0 I) (hk : k ≤ min d.pur I.length) (ho : o = tFreshOracle) :
    tPreOk o (some { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }) := by
  obtain ⟨hH, hu, hp, -, hs⟩ := hd
  have hI0 : I = [] := by
    have := walImg_length_le hI
    rw [hH] at this
    exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp this)
  refine ⟨ho, Or.inr ⟨_, rfl, hI0, ?_, ?_, ?_, hs⟩⟩
  · simp only [hu, Nat.zero_min]
  · simp only [hp, Nat.zero_min]
  · rw [hp, Nat.zero_min] at hk; exact Nat.le_zero.mp hk

end pure

end etcd_wal
end EtcdGrove
end Perennial
