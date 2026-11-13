/-
Extension-level specs of the tree's shared mode that the `os`-level shared specs need and
`GooseLang/Ext/Fs/TreeShared.lean` does not state yet (2026-11-13). **Unproved (`sorry`)**: each
belongs in `TreeShared.lean`, proved there (with `wp_osOpenCreateS`'s existing-file branch, whose
world update it shares); stated here so that the `os` specs over them can be proved meanwhile.
Untrusted.

* `wp_osOpenFileS`: `open(2)` of a name holding a file, without `O_TRUNC` (with or without
  `O_CREAT`, any access mode): no entry, so a fraction of the claim suffices (design §3, "open of
  an existing file without O_CREAT: a fraction of the claim suffices"). The `os` models need it for
  a retried `O_CREAT` open after an attempt that created the file and returned `EINTR`, and for
  `os.OpenFile` of an existing file (the WAL's `LockFile(O_WRONLY)` of a renamed segment,
  `openWALFiles`' `O_RDWR`/`O_RDONLY` opens).
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

/-- **`open(2)` of `d/b`, a name holding the file `i`, without `O_TRUNC`**, with a fraction of a
claim on names containing `b`: no entry; on success a fresh fd on `i`. -/
theorem wp_osOpenFileS (R : Roots) (d b : GoString) (j i : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat)
    (htr : fl.toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗ osNames (L := L) j N dqn h -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd i fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  sorry

end specs

end Fs
end Perennial

end
