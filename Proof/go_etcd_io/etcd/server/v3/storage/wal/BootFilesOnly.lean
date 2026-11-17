/- Lean-first (no Rocq counterpart).

# The crash boot's files-only fact, from the claims a crash keeps (`notes/wal-fsext-w4c-plan.md`, "W4c U3 log", third session)

The crash boot's premise `hfo` (every WAL directory and `nm.<sfx>` directory of the area holds only files)
is to become a fact of the WAL invariant: the invariant keeps a share of the claims under which those
entries sit, each with a history that never holds a directory at its names (`HistNoDir`). A crash leaves
at a claimed name what one of the claim's versions held (`RegionCrashed`, `NamesH.valAfter`): no
directory (`regionCrashed_noDir`). Pure.
-/
module

public import GooseLang.Ext.Fs.NamesGhost
public import Spec.os.RemoveAll

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs

/-- **No version of the history `h` holds a directory at the name `b`**: neither at boot nor after
any of its logged entries. -/
def HistNoDir (h : NamesH) (b : GoString) : Prop :=
  (∀ J, h.boot !! b ≠ some (.dir J)) ∧ ∀ xe ∈ h.ents, ∀ J, xe.2.2 !! b ≠ some (.dir J)

/-- What a crash leaves at a name is one of its history's versions. -/
theorem valAfter_mem (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) :
    h.valAfter j K b = h.boot !! b ∨ ∃ xe ∈ h.ents, h.valAfter j K b = xe.2.2 !! b := by
  unfold NamesH.valAfter
  split
  · rename_i xe hxe
    exact .inr ⟨xe, (List.mem_filter.1 (List.mem_of_getLast? hxe)).1, rfl⟩
  · exact .inl rfl

/-- A history holding no directory at `b` leaves none there after a crash. -/
theorem valAfter_noDir {h : NamesH} {b : GoString} (hn : HistNoDir h b) (j : Ino) (K : Nat → Prop) :
    ∀ J, h.valAfter j K b ≠ some (.dir J) := by
  intro J
  rcases valAfter_mem h j K b with e | ⟨xe, hxe, e⟩ <;> rw [e]
  · exact hn.1 J
  · exact hn.2 xe hxe J

/-- **A claimed name whose history holds no directory holds none after the crash.** -/
theorem regionCrashed_noDir {cl : List Claim} {n : Nat} {m' : Tree} (hr : RegionCrashed cl n m')
    {c : Claim} (hc : c ∈ cl) {b : GoString} (hb : c.2.1.Mem b) (hn : HistNoDir c.2.2 b) :
    ∀ J, m'.entry c.1 b ≠ some (.dir J) := by
  obtain ⟨K, -, -, hK⟩ := hr
  rw [hK c hc b hb]
  exact valAfter_noDir hn c.1 K

/-- A history's new version holding no directory at `b` keeps `HistNoDir`. -/
theorem HistNoDir.log {h : NamesH} {b : GoString} (hn : HistNoDir h b) (x : Nat) (e : LogEntry)
    (E : Ents) (hE : ∀ J, E !! b ≠ some (.dir J)) : HistNoDir (h.log x e E) b := by
  refine ⟨hn.1, fun xe hxe J => ?_⟩
  simp only [NamesH.log, List.mem_append, List.mem_singleton] at hxe
  rcases hxe with hxe | rfl
  · exact hn.2 xe hxe J
  · exact hE J

/-- **A directory every name of which a crash-kept claim covers with a history holding no directory
holds only files after the crash** (the crash boot's `hfo`, for one directory). -/
theorem regionCrashed_filesOnly {cl : List Claim} {n : Nat} {m' : Tree} (hr : RegionCrashed cl n m')
    (J : Ino) (hcov : ∀ b, ∃ c ∈ cl, c.1 = J ∧ c.2.1.Mem b ∧ HistNoDir c.2.2 b) :
    FilesOnly (entsOf m' J) := by
  intro b nd he
  obtain ⟨c, hc, hcJ, hb, hn⟩ := hcov b
  have hl : entsOf m' J !! b = m'.entry J b := by
    unfold entsOf Tree.entry
    cases m' !! J <;> rfl
  rw [hl] at he
  cases nd with
  | file i => exact ⟨i, rfl⟩
  | dir J' =>
    subst hcJ
    exact absurd he (regionCrashed_noDir hr hc hb hn J')

end WalFs
end EtcdGrove
end Perennial

end
