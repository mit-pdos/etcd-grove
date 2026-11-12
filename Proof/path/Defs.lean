/-
**`Clean`'s lazy buffer** (`path.lazybuf`; rafthttp stage 5d). Lean-first.

`lbOwn b p P w`: the buffer `b` over the path `p` holds `P` (`P.take w`, its first `w` bytes, is
`Clean`'s output so far): `p` itself while `buf` is `nil` (the output is a prefix of the path), or
`buf`'s bytes once it is made, as long as `p`. Bytes of `P` past `w` stay readable: `Clean`'s
backtracking lowers `w` and reads them (`index`).
-/
module

public import Proof.path.Model
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The lazy buffer `b` over `p`, holding `P`, written up to `w`** (exclusive). -/
def path.lbOwn (b : Loc) (p : GoString) (P : List w8) (w : Nat) : IProp GF :=
  iprop(∃ buf : GoSlice, b.[_root_.Perennial.path.lazybuf, go!"s"] ↦ p ∗
    b.[_root_.Perennial.path.lazybuf, go!"buf"] ↦ buf ∗
    b.[_root_.Perennial.path.lazybuf, go!"w"] ↦ W64 (w : Int) ∗
    ⌜w ≤ p.length ∧ p.length < 2 ^ 63⌝ ∗
    (⌜buf = slice.nil ∧ P = p⌝ ∨ ⌜buf ≠ slice.nil ∧ P.length = p.length⌝ ∗ buf ↦* P))

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
open Iris.ProofMode

/-- **`b.w`**, to read or write: the buffer at any `w'` up to the path's length once it is back. -/
theorem path.lbOwn_w (b : Loc) (p : GoString) (P : List w8) (w : Nat) :
    path.lbOwn (GF := GF) b p P w ⊢
      b.[_root_.Perennial.path.lazybuf, go!"w"] ↦ W64 (w : Int) ∗
      ⌜w ≤ p.length ∧ p.length < 2 ^ 63 ∧ P.length = p.length⌝ ∗
      (∀ w' : Nat, ⌜w' ≤ p.length⌝ -∗ b.[_root_.Perennial.path.lazybuf, go!"w"] ↦ W64 (w' : Int) -∗
        path.lbOwn b p P w') := by
  iintro Hb
  iunfold path.lbOwn at Hb
  icases Hb with ⟨%buf, Hs, Hbuf, Hw, %Hwb, Hcase⟩
  ihave %HPl : ⌜P.length = p.length⌝ $$ [Hcase]
  · icases Hcase with (⟨-, %HP⟩ | ⟨⟨-, %HP⟩, -⟩)
    · ipureintro; rw [HP]
    · ipureintro; exact HP
  iframe Hw
  isplitr
  · ipureintro; exact ⟨Hwb.1, Hwb.2, HPl⟩
  iintro %w' %Hw' Hw
  iunfold path.lbOwn
  iexists buf
  iframe
  ipureintro; exact ⟨Hw', Hwb.2⟩

end lemmas

end EtcdGrove
end Perennial
