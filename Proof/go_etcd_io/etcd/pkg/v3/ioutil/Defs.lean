/-
`pkg/ioutil`'s exact-length reader (`readcloser.go`: `NewExactReadCloser`, `exactReadCloser`'s
`Read` and `Close`), the wrapper `snap.NewMessage` put around a snapshot message's database stream
until etcd PR #21569 (branch `pr-verify/etcd-21569`, report `notes/pr-verify/etcd-21569.md`).
Lean-first (no Rocq counterpart).

**The underlying reader** (`readerSpec x R Buf`, persistent): the interface value `x`'s
`Read(p)`, with the reader's state `R k` (`k`: the bytes it has delivered so far) and the
caller's buffer `Buf p`, returns a count `n` with `0 ≤ n ≤ len(p)` and some error, and its state
becomes `R (k + n)`. Nothing is said of the error: `io.Reader` allows any (`io.EOF` with `n > 0`
too). **The underlying closer** (`closerSpec x C`): `Close()` with `C` returns some error.

**The exact reader's outcome** (`exactReadResult br' total n n' err err'`): after the underlying
read of `n` bytes (`err` its error), with `br'` the bytes read in all, `Read` returns `(n', err')`:
`(0, ErrExpectEOF)` past the total; `(0, ErrShortRead)` short of it on an empty read; else the
underlying result unchanged (then `br' ≤ total`, and `br' = total` if `n = 0`: `exact_end`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.ioutil.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The interface value `x` is a reader** (persistent), its state `R k` after `k` bytes
delivered, the caller's buffer `Buf p`: `Read(p)` returns `n` bytes, `0 ≤ n ≤ len(p)`, and some
error. -/
def readerSpec (x : GoInterfaceOk) (R : Nat → IProp GF) (Buf : GoSlice → IProp GF) : IProp GF :=
  iprop(□ (∀ (k : Nat) (p : GoSlice),
    {{ R k ∗ Buf p }}
      (App (Val #(methods x.ty go!"Read" x.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        R (k + sint.nat n) ∗ Buf p ∗ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z p.len⌝ }}))

instance readerSpec_persistent (x : GoInterfaceOk) (R : Nat → IProp GF) (Buf : GoSlice → IProp GF) :
    Persistent (readerSpec x R Buf) := by
  unfold readerSpec; infer_instance

/-- **The interface value `x` is a closer** (persistent): `Close()`, with `C`, returns some
error. -/
def closerSpec (x : GoInterfaceOk) (C : IProp GF) : IProp GF :=
  iprop(□ ({{ C }} (App (Val #(methods x.ty go!"Close" x.v)) (Val #()))
    {{ (err : GoInterface), RET #err; True }}))

instance closerSpec_persistent (x : GoInterfaceOk) (C : IProp GF) :
    Persistent (closerSpec x C) := by
  unfold closerSpec; infer_instance

/-- **What the exact reader's `Read` returns** (`(n', err')`), the underlying read having
returned `(n, err)` and `br'` bytes having been read in all, of `total` expected: past the total,
`(0, ErrExpectEOF)`; short of it on an empty read, `(0, ErrShortRead)`; else `(n, err)`. -/
def exactReadResult (br' total n n' : w64) (err err' : GoInterface) : IProp GF :=
  iprop((⌜sint.Z total < sint.Z br' ∧ n' = W64 0⌝ ∗
      globalAddr ioutil.ErrExpectEOF ↦□ err') ∨
    (⌜sint.Z br' < sint.Z total ∧ n = W64 0 ∧ n' = W64 0⌝ ∗
      globalAddr ioutil.ErrShortRead ↦□ err') ∨
    ⌜sint.Z br' ≤ sint.Z total ∧ ¬ (sint.Z br' < sint.Z total ∧ n = W64 0) ∧ n' = n ∧
      err' = err⌝)

/-- **The exact reader's guarantee**: a result passed through unchanged from an empty
underlying read (the only way `io.Pipe`, the snapshot stream's reader, reports its end) comes
after exactly `total` bytes. -/
theorem exact_end (br' total n : w64)
    (h : sint.Z br' ≤ sint.Z total ∧ ¬ (sint.Z br' < sint.Z total ∧ n = W64 0))
    (hn : n = W64 0) : sint.Z br' = sint.Z total := by
  obtain ⟨h1, h2⟩ := h
  have : ¬ sint.Z br' < sint.Z total := fun hlt => h2 ⟨hlt, hn⟩
  omega

end defs

end EtcdGrove
end Perennial
