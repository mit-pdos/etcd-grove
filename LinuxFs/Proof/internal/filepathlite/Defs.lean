/-
**`Clean`'s lazy buffer** (`internal/filepathlite.lazybuf`, the part's translation; WAL leaf specs,
2026-11-13). Lean-first; as the main tree's `path.lbOwn` (`Proof/path/Defs.lean`), with the two
fields `filepathlite`'s buffer adds fixed to what `Clean` sets them to on Unix: `volAndPath` the
path itself and `volLen` zero (`volumeNameLen` is `0`).

`lbOwn b p P w`: the buffer `b` over the path `p` holds `P` (`P.take w`, its first `w` bytes, is
`Clean`'s output so far): `p` itself while `buf` is `nil`, or `buf`'s bytes once it is made, as
long as `p`.
-/
module

public import Proof.path.Model
public import LinuxFs.Proof.internal.filepathlite.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The lazy buffer `b` over `p`, holding `P`, written up to `w`** (exclusive). -/
def filepathlite.lbOwn (b : Loc) (p : GoString) (P : List w8) (w : Nat) : IProp GF :=
  iprop(∃ buf : GoSlice, b.[_root_.Perennial.internal.filepathlite.lazybuf, go!"path"] ↦ p ∗
    b.[_root_.Perennial.internal.filepathlite.lazybuf, go!"buf"] ↦ buf ∗
    b.[_root_.Perennial.internal.filepathlite.lazybuf, go!"w"] ↦ W64 (w : Int) ∗
    b.[_root_.Perennial.internal.filepathlite.lazybuf, go!"volAndPath"] ↦ p ∗
    b.[_root_.Perennial.internal.filepathlite.lazybuf, go!"volLen"] ↦ W64 0 ∗
    ⌜w ≤ p.length ∧ p.length < 2 ^ 63⌝ ∗
    (⌜buf = slice.nil ∧ P = p⌝ ∨ ⌜buf ≠ slice.nil ∧ P.length = p.length⌝ ∗ buf ↦* P))

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
open Iris.ProofMode

/-- **`b.w`**, to read or write: the buffer at any `w'` up to the path's length once it is back. -/
theorem filepathlite.lbOwn_w (b : Loc) (p : GoString) (P : List w8) (w : Nat) :
    filepathlite.lbOwn (GF := GF) b p P w ⊢
      b.[_root_.Perennial.internal.filepathlite.lazybuf, go!"w"] ↦ W64 (w : Int) ∗
      ⌜w ≤ p.length ∧ p.length < 2 ^ 63 ∧ P.length = p.length⌝ ∗
      (∀ w' : Nat, ⌜w' ≤ p.length⌝ -∗
        b.[_root_.Perennial.internal.filepathlite.lazybuf, go!"w"] ↦ W64 (w' : Int) -∗
        filepathlite.lbOwn b p P w') := by
  iintro Hb
  iunfold filepathlite.lbOwn at Hb
  icases Hb with ⟨%buf, Hs, Hbuf, Hw, Hv, Hvl, %Hwb, Hcase⟩
  ihave %HPl : ⌜P.length = p.length⌝ $$ [Hcase]
  · icases Hcase with (⟨-, %HP⟩ | ⟨⟨-, %HP⟩, -⟩)
    · ipureintro; rw [HP]
    · ipureintro; exact HP
  iframe Hw
  isplitr
  · ipureintro; exact ⟨Hwb.1, Hwb.2, HPl⟩
  iintro %w' %Hw' Hw
  iunfold filepathlite.lbOwn
  iexists buf
  iframe
  ipureintro; exact ⟨Hw', Hwb.2⟩

end lemmas

end EtcdGrove
end Perennial
