/-
**An `io.Writer` written as a stream** (WAL W6, 2026-11-13): the vocabulary of the specs of
`ioutil.PageWriter` (`LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/ioutil/`), which the WAL's encoder writes
through (encoder.go: `write`, `e.bw.Flush()`), over a `*os.File`.

* `io.writerStream wi W` (persistent): `wi.Write(p)`, from the state `W out` (`out` the bytes it has
  accepted so far), accepts a prefix `ys` of `p`'s bytes, leaves `W (out ++ ys)` and returns
  `len(ys)`; all of them unless it returns an error (`io.Writer`'s contract: "Write must return a
  non-nil error if it returns n < len(p)"); `p` is only read. The client chooses `W` (what the
  bytes become: a file's content from an offset, ...).
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
def io.writerStream (wi : GoInterfaceOk) (W : List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (out : List w8) (p : GoSlice) (xs : List w8) (dq : DFrac),
    {{ W out ∗ p ↦*{dq} xs }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜ys <+: xs ∧ sint.Z n = ys.length ∧ (err = GoInterface.nil → ys = xs)⌝ ∗
        W (out ++ ys) ∗ p ↦*{dq} xs }})

instance io.writerStream_persistent (wi : GoInterfaceOk) (W : List w8 → IProp GF) :
    Persistent (io.writerStream wi W) := by
  unfold io.writerStream; infer_instance

end defs

end EtcdGrove
end Perennial
