/-
Lean-first (no Rocq counterpart).

# `bytes.Buffer`: the trust boundary of its uses (2026-10-22, `notes/k8s-etcd3-plan.md` stage 6c)

Perennial translates `bytes.Buffer` as a struct (its fields `buf`, `off`, `lastRead`) but not the
bodies of `Write` and `Bytes`, and has no specs of them (`notes/perennial-changes.md`, "Standard
library: packages not translated, and functions without specs"). apimachinery's `runtime.Encode`
writes an object's encoding into a fresh `bytes.Buffer` and returns `Bytes()`. Until Perennial
specifies them, `Spec/bytes/Buffer__Write.lean` and `Spec/bytes/Buffer__Bytes.lean` are axioms over:

- `ownBuffer b bs`: the buffer at `b` holds the unread bytes `bs`, defined from the struct's fields
  as Go's comment on `Buffer` says ("contents are the bytes buf[off : len(buf)]"), owning `buf`'s
  spare capacity (which `Write` grows into) -- Perennial's `bytes.ownBuffer` with the capacity;
- `ownBuffer_new`: a zero `Buffer` (what `&bytes.Buffer{}` allocates) is an empty buffer, a theorem
  (until 2026-11-21 `ownBuffer` was opaque and this an axiom).

The axioms hold of Go's `bytes.Buffer`: `Write` appends (and never fails: it panics only when the
buffer outgrows memory, `ErrTooLarge`), `Bytes` returns the unread bytes.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bufferM

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The `*Buffer` at `b` holds the unread bytes `bs`** (exclusive): its slice `buf` holds `all`,
with `buf`'s spare capacity, and its read offset `off` is within it, with `bs = all[off:]` (see the
file header). -/
def ownBuffer (b : Loc) (bs : List w8) : IProp GF :=
  iprop(∃ (v : _root_.Perennial.bytes.Buffer) (all : List w8), b ↦ v ∗ v.buf' ↦* all ∗
    ownSliceCap w8 v.buf' (DFrac.own 1) ∗
    ⌜0 ≤ sint.Z v.off' ∧ sint.nat v.off' ≤ all.length ∧ bs = all.drop (sint.nat v.off')⌝)

/-- **A zero `Buffer` is empty**: its `buf` is the nil slice, its offset 0. -/
theorem ownBuffer_new (b : Loc) :
    b ↦ (zero_val _root_.Perennial.bytes.Buffer) ⊢ ownBuffer (GF := GF) b [] := by
  iintro Hb
  unfold ownBuffer
  ihave Hs := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hc := ownSliceCap_nil (V := w8) (GF := GF)
  have hbuf : (zero_val _root_.Perennial.bytes.Buffer).buf' = slice.nil := rfl
  have hoff : (zero_val _root_.Perennial.bytes.Buffer).off' = 0 := rfl
  iexists (zero_val _root_.Perennial.bytes.Buffer), []
  rw [hbuf, hoff]
  isplitl [Hb]
  · iexact Hb
  isplitl [Hs]
  · iexact Hs
  isplitl [Hc]
  · iexact Hc
  ipureintro
  exact ⟨by decide, by decide, rfl⟩

end defs

end bufferM
end EtcdGrove
end Perennial
