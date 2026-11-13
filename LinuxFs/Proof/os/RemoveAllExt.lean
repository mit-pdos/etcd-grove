/-
Extension-level steps of the tree's shared mode that `os.RemoveAll`'s proof needs and
`GooseLang/Ext/Fs/TreeShared.lean` does not state (2026-11-13). Untrusted.

* `wp_osRmdirS_nonempty`: `rmdir(2)` of `d/b`, a directory `J` with a name there (a fraction of a
  claim on names of `J` showing it), with fractions of the spines to `d` and to `d/b`: an errno, no
  effect (the semantics' `Rmdir` takes effect only on an empty directory, `EmptyDir`).
  `RemoveAll`'s last `rmdir` meets it when an `unlink` of a file failed.
-/
module

public import LinuxFs.Proof.os.SharedExt

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

/-- **`rmdir(2)` of `d/b`, a directory `J` holding the name `c`** (a fraction of a claim on names
`N ∋ c` of `J`), with spines to `d` and to `d/b`: an errno, no effect. -/
theorem wp_osRmdirS_nonempty (R : Roots) (d b : GoString) (j J : Ino) (N : NameSet)
    (dq dqJ dqn : DFrac) (hJ : NamesH) (c : GoString) (k s0 : Nat) (q : Qp) (hb : NameOk b)
    (hN : N.Mem c) (hc : (hJ.cur !! c).isSome) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osPathS (L := L) R (child d b) dqJ J -∗
      osNames (L := L) J N dqn hJ -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osPathS (L := L) R (child d b) dqJ J -∗ osNames (L := L) J N dqn hJ -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  let P : OsState → Prop := fun st => st.lookup d = some (.dir j) ∧
    st.lookup (child d b) = some (.dir J) ∧ ∀ x, N.Mem x → st.tree.entry J x = hJ.cur !! x
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 → P st →
      ∃ e', IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, k, s0, rfl, treeName_child hp.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 → P st →
      IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' _ _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rcases hres with ⟨J', -, -, ⟨hl, hempty⟩, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [hp.2.1] at hl
      cases hl
      have := hempty c
      rw [hp.2.2 c hN] at this
      rw [this] at hc; exact absurd hc (by simp)
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  have hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗
        iprop(osPathS (L := L) R d dq j ∗ osPathS (L := L) R (child d b) dqJ J ∗
          osNames (L := L) J N dqn hJ) -∗ ⌜P st⌝ := by
    intro st Γn hR hcoh
    iintro HA ⟨Hp, Hp', Hn⟩
    icases osPathS_lookup hR hcoh d dq j $$ HA Hp with %h1
    icases osPathS_lookup hR hcoh (child d b) dqJ J $$ HA Hp' with %h2
    icases osNames_entry hcoh J N dqn hJ $$ HA Hn with %h3
    ipureintro; exact ⟨h1, h2, h3⟩
  iintro #Hinv #Hsi Hp Hp' Hn Hk HΦ
  iapply wp_callEndS "Rmdir" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osPathS (L := L) R (child d b) dqJ J ∗
      osNames (L := L) J N dqn hJ)
    P (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e) hF hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hp' Hn] Hk
  · iframe
  iintro %w %hW Hq ⟨Hp, Hp', Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hp' Hn

end specs

end Fs
end Perennial
