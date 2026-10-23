/-
Lean-first (no Rocq counterpart).

# `bytes.Buffer`: the trust boundary of its uses (2026-10-22, `notes/k8s-etcd3-plan.md` stage 6c)

Perennial translates `bytes.Buffer` as a struct (its fields `buf`, `off`, `lastRead`) but not its
methods' bodies, and has no specs of them (`notes/perennial-changes.md`, "Standard library:
packages not translated, and functions without specs"). apimachinery's `runtime.Encode` writes an
object's encoding into a fresh `bytes.Buffer` and returns `Bytes()`. Until Perennial specifies
`bytes.Buffer`, this repository states what those uses need as axioms, here and in the specs of
`Spec/bytes/Buffer__Write.lean` and `Spec/bytes/Buffer__Bytes.lean`:

- `ownBuffer b bs` (an opaque resource): the buffer at `b` holds the bytes `bs`;
- `ownBuffer_new`: a zero `Buffer` (what `&bytes.Buffer{}` allocates) is an empty buffer.

They hold of Go's `bytes.Buffer`: `Write` appends (and never fails: it panics only when the
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

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The buffer at `b` holds the bytes `bs` (opaque). -/
opaque ownBuffer (b : Loc) (bs : List w8) : IProp GF

/-- **A zero `Buffer` is empty** (the trust boundary; see the file header). -/
axiom ownBuffer_new [bytes.Assumptions] (b : Loc) :
    b ↦ (zero_val _root_.Perennial.bytes.Buffer) ⊢ ownBuffer (GF := GF) b []

end defs

end bufferM
end EtcdGrove
end Perennial
