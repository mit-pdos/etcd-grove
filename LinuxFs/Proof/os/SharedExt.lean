/-
Extension-level steps of the tree's shared mode that the `os`-level shared specs need and
`GooseLang/Ext/Fs/TreeShared.lean` does not state (2026-11-13). Untrusted.

* `wp_osMkdirS_some`: `mkdir(2)` of a name holding something (a file or a directory), with a
  fraction of a claim on names containing it: an errno, no effect (the semantics' `Mkdir` takes
  effect only on an absent name). `os.Mkdir`'s retry after an attempt that made the directory and
  returned `EINTR` meets it.
* `wp_osOpenAbsentS`: `open(2)` without `O_CREAT` of a name holding nothing, with a fraction of a
  claim on names containing it: an errno, no effect (`os.Stat` of an absent name).
* `osLogLb_0`: a lower bound on the log's length to begin a call with.
-/
module

public import LinuxFs.Proof.os.SharedAu

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`mkdir(2)` of `d/b`, a name holding something**, with a fraction of a claim on names
containing `b`: an errno, no effect. -/
theorem wp_osMkdirS_some (R : Roots) (d b : GoString) (j : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : (h.cur !! b).isSome) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j N dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Mkdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      ∃ e', IsFsStep "Mkdir" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, k, s0, rfl, treeName_child hp.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      IsFsStep "Mkdir" (PairV (osTokV k) (#(child d b))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rcases hres with ⟨j', b', hl, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [pathNames_child hw hp hb hN] at hl; rw [hl] at hi; exact absurd hi (by simp)
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "Mkdir" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j N dqn h)
    (fun st => PathNames st d j N h) (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hn

/-- **`open(2)` without `O_CREAT` of `d/b`, a name holding nothing**, with a fraction of a claim on
names containing `b`: an errno, no effect. -/
theorem wp_osOpenAbsentS (R : Roots) (d b : GoString) (j : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat)
    (hcr : fl.toNat / O_CREAT % 2 = 0) (htr : fl.toNat / O_TRUNC % 2 = 0) (hb : NameOk b)
    (hN : N.Mem b) (hi : h.cur !! b = none) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j N dqn h -∗ Φ (PairV (#(-1 : w64)) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = false := by simp [htr]
  have hcr' : decide ((fl.toNat / O_CREAT) % 2 = 1) = false := by simp [hcr]
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      ∃ e', IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e'
        (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, .inl ⟨child d b, fl, k, s0, rfl, .inr (treeName_child hp.1 hb), hfl,
      hcall, fun h => absurd h (by simp [htr']), .inr ⟨1, by decide, rfl, .inl rfl⟩⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = PairV (#(-1 : w64)) (#e) := by
    intro st e' st' hw _ _ hp Hst
    have hl : (st.metaEnd k).lookup (child d b) = none := by
      show st.lookup (child d b) = none
      rw [pathNames_child hw hp hb hN]; exact hi
    simp only [IsFsStep] at Hst
    replace Hst := open_inTree Hst (.inr (treeName_child hp.1 hb))
    obtain ⟨p', fl', k', s', hv, -, -, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl, rfl⟩ := tokPathFl_inj hv
    rcases hres with ⟨st1, tgt, fd, hoe, -⟩ | ⟨e, he0, rfl, hst'⟩
    · simp only [OpenEffect, hl, hcr', Bool.false_eq_true, false_and] at hoe
    · rcases hst' with rfl | ⟨tgt, hoe⟩
      · exact ⟨rfl, _, rfl, e, he0, rfl⟩
      · simp only [OpenEffect, hl, hcr', Bool.false_eq_true, false_and] at hoe
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "Open" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j N dqn h)
    (fun st => PathNames st d j N h)
    (fun w => ∃ e : w64, e ≠ 0 ∧ w = PairV (#(-1 : w64)) (#e))
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hn

end specs

section lb
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The log has at least no entries. -/
theorem osLogLb_0 : ⊢ |==> osLogLb (L := L) 0 := by
  unfold osLogLb
  letI := (gooseOsGS (L := L)).osAllG
  exact monoNatLbOwn_0 _

end lb

end Fs
end Perennial

end
