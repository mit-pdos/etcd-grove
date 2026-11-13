/-
**An `io.Writer` written as a stream** (WAL W6, 2026-11-13): the vocabulary of the specs of
`ioutil.PageWriter` (`LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/ioutil/`), which the WAL's encoder writes
through (encoder.go: `write`, `e.bw.Flush()`), over a `*os.File`.

* `io.writerStream wi lim W B` (persistent): `wi.Write(p)`, from the state `W out` (`out` the bytes it
  has accepted so far), either accepts all of `p`'s bytes `xs`, leaves `W (out ++ xs)` and returns
  `(len(p), nil)`, or returns an error, leaving the writer broken: `B out xs`, the client's
  predicate of a failed write of `xs` after `out` (what the bytes become then: a file's content
  with some prefix of `xs` written and its offset lost, ...), and any count; `p` is only read. The
  client chooses `W` and `B`. A client that stops at a write error (the WAL: its encoder's
  error ends the `Save`, and the WAL is not written again) loses nothing: `B` is what the writer's
  own spec says of a failed write. The writer accepts at most `lim` bytes in all
  (`out ++ xs`): a file's model does not go past `2^62`. (`io.Writer`'s contract, "Write must return a non-nil error if
  it returns n < len(p)", allows the count of an error to be the bytes written; `os.File`'s
  trusted model does not keep it, `LinuxFs/TrustedCode/os.lean`'s `File.Write.impl`, so the
  stream says nothing of it.) Until 2026-11-13 (`wal-bridge`) the error left `W (out ++ ys)`,
  `ys` a prefix of `xs` and `n = len(ys)`, which a file whose offset a failed `Write` loses (the
  model's `-1`) cannot give.
Lean-first.
-/
module

public import Perennial.Proof.io

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

/-- See the file header. -/
def io.writerStream (wi : GoInterfaceOk) (lim : Nat) (W : List w8 → IProp GF)
    (B : List w8 → List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (out : List w8) (p : GoSlice) (xs : List w8) (dq : DFrac),
    ⌜out.length + xs.length ≤ lim⌝ →
    {{ W out ∗ p ↦*{dq} xs }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); p ↦*{dq} xs ∗
        ((⌜err = GoInterface.nil ∧ sint.Z n = xs.length⌝ ∗ W (out ++ xs)) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ B out xs)) }})

instance io.writerStream_persistent (wi : GoInterfaceOk) (lim : Nat) (W : List w8 → IProp GF)
    (B : List w8 → List w8 → IProp GF) : Persistent (io.writerStream wi lim W B) := by
  unfold io.writerStream; infer_instance

end defs

end EtcdGrove
end Perennial
