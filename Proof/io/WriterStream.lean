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
  model's `-1`) cannot give. The error is `errOkOrNil` (an error `fmt` formats by its `Error()`
  alone: fmt soundness, 2026-11-18, so that the WAL's `fmt.Errorf("%w (after: %v)", ...)` of a
  sync's error meets `fmt.ErrorfErrs.spec`'s premise); `*os.File`'s errors (`*fs.PathError`) are.
Lean-first.
-/
module

public import Perennial.Proof.io
public import Spec.fmt.ErrorfErrs

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
         (⌜err ≠ GoInterface.nil⌝ ∗ errOkOrNil err ∗ B out xs)) }})

instance io.writerStream_persistent (wi : GoInterfaceOk) (lim : Nat) (W : List w8 → IProp GF)
    (B : List w8 → List w8 → IProp GF) : Persistent (io.writerStream wi lim W B) := by
  unfold io.writerStream; infer_instance

/-- **A stream writer whose acceptance is guarded** (WAL W6, 2026-11-13): `io.writerStream` with
the length bound generalized to a predicate `ok` of the whole stream (`out ++ xs`), which the
client keeps prefix-closed: a crash-tracked file (the WAL's tail) accepts only the bytes it is meant
to hold (`ok ys := ys <+: T`), since writing others would break its crash invariant. -/
def io.writerStreamP (wi : GoInterfaceOk) (ok : List w8 → Prop) (W : List w8 → IProp GF)
    (B : List w8 → List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (out : List w8) (p : GoSlice) (xs : List w8) (dq : DFrac),
    ⌜ok (out ++ xs)⌝ →
    {{ W out ∗ p ↦*{dq} xs }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); p ↦*{dq} xs ∗
        ((⌜err = GoInterface.nil ∧ sint.Z n = xs.length⌝ ∗ W (out ++ xs)) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ errOkOrNil err ∗ B out xs)) }})

instance io.writerStreamP_persistent (wi : GoInterfaceOk) (ok : List w8 → Prop)
    (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF) :
    Persistent (io.writerStreamP wi ok W B) := by
  unfold io.writerStreamP; infer_instance

/-- **A guarded stream writer called only with bytes** (unit `noioerr`, 2026-11-15): `io.writerStreamP`
for the calls with a non-empty `xs`, nothing said of an empty `Write`. A client that never hands its
writer an empty slice (the page writer: `flush` writes only a non-empty buffer, `Write` only whole
pages) is specified over it, so that a writer whose empty `Write` may fail for no reason (`*os.File`:
the trusted model's empty-write branch draws an arbitrary errno with no `fsExt` step,
`os.File.Write.wp_empty`) can still be one whose every call succeeds (`B` false: the tail's writer under
`NoIoErr`). `io.writerStreamP_NE`: every guarded stream is one. -/
def io.writerStreamPNE (wi : GoInterfaceOk) (ok : List w8 → Prop) (W : List w8 → IProp GF)
    (B : List w8 → List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (out : List w8) (p : GoSlice) (xs : List w8) (dq : DFrac),
    ⌜ok (out ++ xs)⌝ → ⌜xs ≠ []⌝ →
    {{ W out ∗ p ↦*{dq} xs }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); p ↦*{dq} xs ∗
        ((⌜err = GoInterface.nil ∧ sint.Z n = xs.length⌝ ∗ W (out ++ xs)) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ errOkOrNil err ∗ B out xs)) }})

instance io.writerStreamPNE_persistent (wi : GoInterfaceOk) (ok : List w8 → Prop)
    (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF) :
    Persistent (io.writerStreamPNE wi ok W B) := by
  unfold io.writerStreamPNE; infer_instance

/-- Every guarded stream writer is one called only with bytes. -/
theorem io.writerStreamP_NE (wi : GoInterfaceOk) (ok : List w8 → Prop) (W : List w8 → IProp GF)
    (B : List w8 → List w8 → IProp GF) :
    io.writerStreamP wi ok W B ⊢ io.writerStreamPNE wi ok W B := by
  unfold io.writerStreamP io.writerStreamPNE
  iintro #Hw
  imodintro
  iintro %out %p %xs %dq %hok %_
  iapply Hw $$ %out %p %xs %dq %hok

/-- `io.writerStream` is the guarded stream of the length bound. -/
theorem io.writerStream_P (wi : GoInterfaceOk) (lim : Nat) (W : List w8 → IProp GF)
    (B : List w8 → List w8 → IProp GF) :
    io.writerStream wi lim W B ⊣⊢ io.writerStreamP wi (fun ys => ys.length ≤ lim) W B := by
  unfold io.writerStream io.writerStreamP
  simp only [List.length_append]
  exact .rfl

end defs

end EtcdGrove
end Perennial
