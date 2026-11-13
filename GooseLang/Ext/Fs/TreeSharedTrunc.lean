/-
The shared mode of the tree: `open(2)` with `O_TRUNC` of a name holding a file (`wp_osOpenTruncS`),
for the WAL's `filePipeline.alloc` (`O_CREATE|O_TRUNC` of `N.tmp`, which may be left over from an
earlier run). Untrusted.

The semantics (`OpenEffect`, `Impl.lean`): an existing file is truncated to size 0 in the open's
step (the change `OsChange.ofResize i f 0` announced and landed at once, stamped), no entry logged;
on failure the truncation may or may not have happened; the step needs no change in flight on the
file (`¬ BusyAt`), which the file's whole `OsMeta` gives (`tokRes_meta_whole`). So the spec takes
what a resize's first step takes (`wp_osResizeStart` with target 0: the `OsMeta`, the bytes it cuts
off, the client's halves of the mapped cells) and gives back what its landing gives
(`rsDone i 0 0 m n`), or, without the truncation, what it took.

`O_CREAT|O_TRUNC` of an absent name is `wp_osOpenCreateS'` (`TreeSharedCreate.lean`), whose `O_TRUNC`
premise is "clear, or the name absent".

**`wp_osOpenTruncS` is `sorry`** (2026-11-13, branch `wal-osau3`): its proof needs the one-step
world update of a landed resize (`osCoh_start` then `resize_done_world`, `Truncate.lean`, composed
in one step, with the state `st.stampFile i (fun n => (f.announce c n).land c c.hi 0)`), on top of
`wp_osOpenFileS'`'s tree part. `notes/wal-fsext-i2-design.md`, implementation log.
-/
module

public import GooseLang.Ext.Fs.TreeSharedCreate
public import GooseLang.Ext.Fs.Truncate

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

/-- No mapped cell in an empty range. -/
theorem mcellsAny_empty (M : GMap Loc Nat) (n : Nat) : ⊢ mcellsAny (GF := GF) M n n := by
  unfold mcellsAny
  refine (BigSepM.bigSepM_intro (P := (emp : IProp GF)) ?_)
  intro b len _
  iintro -
  iexists (fun _ => (#() : val))
  unfold cellsR
  rw [Nat.sub_self]
  simp only [List.range'_zero]
  iempintro

/-- **`open(2)` with `O_TRUNC` of `d/b`, a name holding the file `i`** (shared mode; any access
mode, with or without `O_CREAT`), with a fraction of a claim on names containing `b`, the file's
`OsMeta` whole, its bytes and the client's halves of its mapped cells: no entry logged; the file
truncated (`rsDone i 0 0 m n`), or, on failure only, left as it was; on success a fresh fd on `i`.
**`sorry`** (the file header). -/
theorem wp_osOpenTruncS (R : Roots) (d b : GoString) (j i : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (m : OsMeta) (xs : List ByteG)
    (hfl : OpenFlagsOk fl.toNat) (htr : fl.toNat / O_TRUNC % 2 = 1) (hb : NameOk b)
    (hN : N.Mem b) (hi : h.cur !! b = some (.file i)) (hlen : xs.length = m.size)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      osMeta (L := L) i (DFrac.own 1) m -∗ osBytes (L := L) i 0 (DFrac.own 1) xs -∗
      mcellsAny (GF := GF) m.maps 0 m.size -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗ osNames (L := L) j N dqn h -∗
        ((⌜e ≠ 0⌝ ∗ osMeta (L := L) i (DFrac.own 1) m ∗ osBytes (L := L) i 0 (DFrac.own 1) xs ∗
            mcellsAny (GF := GF) m.maps 0 m.size) ∨
         (∃ n, rsDone (L := L) i 0 0 m n)) -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd i fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  sorry

end specs

end Fs
end Perennial

end
