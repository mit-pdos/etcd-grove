/-
Shared definitions of the `os`-level specs of the tree's shared mode (`notes/wal-fsext-i2-design.md`,
review finding M1; `GooseLang/Ext/Fs/TreeShared.lean`): the mask of their atomic updates
(`osAuMask`: everything but the extension's invariants), the opening of such an update around one
step of the extension (`wp_au_step`: abort with the precondition back, or commit with an outcome),
and the extension-level steps the `os` models need beyond `TreeShared.lean`'s (`LstatDir` with a
claim on any names containing the path's last component). Untrusted.

How a spec here is shaped: the caller holds a fraction of each claim the call changes (so that
no one else changes the names between the model's attempts) and gives the rest of it to the
atomic update (a crash invariant typically holds that half); the update commits at the
extension step that logs the call's entry, or at the step that ends the call with an error and no
effect, with the outcome (`Option (Nat × Nat)`: the entry's index and its call's start, or none);
an `EINTR` attempt with no effect aborts it, and the model retries.
-/
module

public import GooseLang.Ext.Fs.TreeShared
public import LinuxFs.Proof.os.CrashFile
public import Iris.BI.Lib.Atomic

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The outer mask of the shared `os` specs' atomic updates: all but the extension's invariants. -/
def osAuMask : CoPset := ((⊤ : CoPset) \ ↑osN) \ ↑osShN

theorem osN_sub_au : (↑osN : CoPset) ⊆ (⊤ : CoPset) \ osAuMask := by
  intro x hx
  refine LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun h => ?_⟩
  have h1 := (LawfulSet.mem_diff.1 h).1
  exact (LawfulSet.mem_diff.1 h1).2 hx

theorem osShN_sub_au : (↑osShN : CoPset) ⊆ (⊤ : CoPset) \ osAuMask := by
  intro x hx
  refine LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun h => ?_⟩
  exact (LawfulSet.mem_diff.1 h).2 hx

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem fupd_open_au (P : IProp GF) :
    (|={osAuMask, ∅}=> P) ⊢ |={⊤, (⊤ : CoPset) \ osAuMask}=> P := by
  have h := fupd_mask_frame_right (P := P) (E1 := osAuMask) (E2 := ∅)
    (Ef := (⊤ : CoPset) \ osAuMask) LawfulSet.disjoint_diff_right
  rwa [LawfulSet.subset_union_diff (s₁ := osAuMask) (s₂ := (⊤ : CoPset)) (fun _ _ => CoPset.mem_full), LawfulSet.union_empty_left] at h

theorem fupd_close_au (P : IProp GF) :
    (|={∅, osAuMask}=> P) ⊢ |={(⊤ : CoPset) \ osAuMask, ⊤}=> P := by
  have h := fupd_mask_frame_right (P := P) (E1 := ∅) (E2 := osAuMask)
    (Ef := (⊤ : CoPset) \ osAuMask) (LawfulSet.disjoint_empty_left)
  rwa [LawfulSet.union_empty_left, LawfulSet.subset_union_diff (s₁ := osAuMask) (s₂ := (⊤ : CoPset)) (fun _ _ => CoPset.mem_full)] at h

end au

section step
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The shared `os` specs' atomic updates: precondition `α`, outcome `o` with `β o`, `Q o`. -/
abbrev osAU {A : Type} (α : IProp GF) (β Q : A → IProp GF) : IProp GF :=
  iprop(AU <{ α }> @ osAuMask, ∅ <{ ∀∀ (o : A), β o, COMM Q o }>)

/-- **An atomic update opened around one step of the extension**: the step runs with the update's
precondition `α`, and ends either aborting (`α` back; the update returns) or committing with an
outcome `o` (`β o`; the update's `Q o`). -/
theorem wp_au_step {A : Type} (op : String) (v : val) (α : IProp GF) (β Q : A → IProp GF)
    (Ψ : val → IProp GF) :
    ⊢ osAU α β Q -∗
      (α -∗ WP (ExternalOp fsExt.name op (Val v)) @ ((⊤ : CoPset) \ osAuMask) {{ w,
        (α ∗ (osAU α β Q -∗ Ψ w)) ∨
        (∃ o, β o ∗ (Q o -∗ Ψ w)) }}) -∗
      WP (ExternalOp fsExt.name op (Val v)) {{ Ψ }} := by
  iintro Hau Hk
  unfold osAU
  iapply (wp_atomic (E1 := ⊤) (E2 := (⊤ : CoPset) \ osAuMask))
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  iapply fupd_open_au
  imod Hacc with Hacc
  isimp only [texist_nil] at Hacc
  icases Hacc with ⟨Hα, Hcl⟩
  imodintro
  ihave Hwp := Hk $$ [Hα]
  · irevert Hα
    dsimp only [Std.Tele.app]
    iintro Hα
    iexact Hα
  iapply wp_wand $$ Hwp
  iintro %w Hr
  icases Hr with (⟨Hα, Hw⟩ | ⟨%o, Hβ, Hw⟩)
  · icases Hcl with ⟨Hab, -⟩
    iapply fupd_close_au
    ihave Hau := Hab $$ [Hα]
    · irevert Hα
      dsimp only [Std.Tele.app]
      iintro Hα
      iexact Hα
    imod Hau
    imodintro
    iapply Hw
    iexact Hau
  · icases Hcl with ⟨-, Hco⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
    iapply fupd_close_au
    imod Hco $$ Hβ with HQ
    imodintro
    iapply Hw $$ HQ

/-- A claim split between the caller (`q`) and the atomic update (`r`). -/
theorem osNames_join (j : Ino) (N : NameSet) (q r : Qp) (h : NamesH) (hq : q + r = 1) :
    osNames (L := L) j N (DFrac.own q) h ∗ osNames (L := L) j N (DFrac.own r) h ⊣⊢
      osNames (L := L) j N (DFrac.own 1) h := by
  rw [← hq]; exact (osNames_frac j N q r h).symm

theorem osLogLb_max (a b : Nat) :
    osLogLb (L := L) a ∗ osLogLb (L := L) b ⊢ osLogLb (L := L) (max a b) := by
  rcases Nat.le_total a b with hle | hle
  · rw [Nat.max_eq_right hle]; iintro ⟨-, H⟩; iexact H
  · rw [Nat.max_eq_left hle]; iintro ⟨H, -⟩; iexact H

/-- What an outcome says of the log: nothing (no effect), or the entry `ent s` logged at `x`, by
a call begun at `s ≥ lb`. -/
def logOut (lb : Nat) (ent : Nat → LogEntry) : Option (Nat × Nat) → IProp GF
  | none => iprop(emp)
  | some (x, s) => iprop(⌜lb ≤ s⌝ ∗ osLogged (L := L) x (ent s))

/-- A claim after an outcome: as it was (no effect), or with the entry logged, its names now `c`. -/
def claimOut (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) (ent : Nat → LogEntry) (c : Ents) :
    Option (Nat × Nat) → IProp GF
  | none => osNames (L := L) j N dq h
  | some (x, s) => osNames (L := L) j N dq (h.log x (ent s) c)

instance logOut_persistent (lb : Nat) (ent : Nat → LogEntry) (o : Option (Nat × Nat)) :
    Persistent (logOut (L := L) lb ent o) := by
  unfold logOut osLogged; split <;> infer_instance

end step

/-! ## `LstatDir` with a claim on any names containing the last component -/

section lstat
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `wp_osLstatDirS` with a claim on names `N` containing `b`. -/
theorem wp_osLstatDirS_mem (R : Roots) (d b : GoString) (j : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (hb : NameOk b) (hbN : N.Mem b) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ isDir : w64, ∀ e : w64, ⌜isDir = 1 → (∃ J, h.cur !! b = some (.dir J)) ∧ e ≠ 0⌝ -∗
        osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j N dqn h -∗ Φ (PairV (#isDir) (#e))) -∗
      WP (ExternalOp fsExt.name "LstatDir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E
        {{ Φ }} := by
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      ∃ e', IsFsStep "LstatDir" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, 0, 0, k, s0, rfl, Or.inr (treeName_child hp.1 hb), hcall,
      rfl, .inr rfl, rfl⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      IsFsStep "LstatDir" (PairV (osTokV k) (#(child d b))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ isDir e : w64, w = PairV (#isDir) (#e) ∧
        (isDir = 1 → (∃ J, h.cur !! b = some (.dir J)) ∧ e ≠ 0) := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', isDir, e, k', s', hv, -, -, hst, hres, rfl⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    refine ⟨hst, _, rfl, isDir, e, rfl, fun h1 => ?_⟩
    rcases hres with ⟨⟨J, hJ⟩, -, he0⟩ | h0
    · rw [pathNames_child hw hp hb hbN] at hJ
      exact ⟨⟨J, hJ⟩, he0⟩
    · rw [h0] at h1; exact absurd h1 (by decide)
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "LstatDir" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j N dqn h)
    (fun st => PathNames st d j N h)
    (fun w => ∃ isDir e : w64, w = PairV (#isDir) (#e) ∧
      (isDir = 1 → (∃ J, h.cur !! b = some (.dir J)) ∧ e ≠ 0))
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨isDir, e, rfl, h1⟩ := hW
  iapply HΦ $$ %isDir %e %h1 Hq Hp Hn

end lstat

end Fs
end Perennial

end
