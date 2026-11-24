/-
Lean-first (no Rocq counterpart).

# `bytes.Buffer`: the vocabulary of its uses (2026-10-22, `notes/k8s-etcd3-plan.md` stage 6c)

apimachinery's `runtime.Encode` writes an object's encoding into a fresh `bytes.Buffer` and returns
`Bytes()`. `Spec/bytes/Buffer__Write.lean` and `Spec/bytes/Buffer__Bytes.lean` are stated over the
definitions below, and proved over Perennial's proofs of `Write` and `Bytes` (mit-pdos/perennial#670;
until 2026-11-24 they were axioms here):

- `ownBuffer b bs`: the buffer at `b` holds the unread bytes `bs`, defined from the struct's fields
  as Go's comment on `Buffer` says ("contents are the bytes buf[off : len(buf)]"), owning `buf`'s
  spare capacity (which `Write` grows into): Perennial's `bytes.ownBuffer` (`ownBuffer_eq`);
- `ownBuffer_new`: a zero `Buffer` (what `&bytes.Buffer{}` allocates) is an empty buffer, a theorem
  (until 2026-11-21 `ownBuffer` was opaque and this an axiom).

-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.bytes
public import Perennial.Proof.bytes.BufferBasics

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

/-- `ownBuffer` is Perennial's `bytes.ownBuffer` (mit-pdos/perennial#670), which `Write`'s and
`Bytes`' proved specs are stated over. -/
theorem ownBuffer_eq [_root_.Perennial.bytes.Assumptions] (b : Loc) (bs : List w8) :
    ownBuffer (GF := GF) b bs = _root_.Perennial.bytes.ownBuffer b bs := rfl

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
