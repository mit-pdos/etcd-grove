/-
**An `io.Writer` and its contract, with short writes** (dsv-bufio, 2026-11-23, mit-pdos/etcd-grove#24):
the vocabulary of the specs of `*bufio.Writer` (`Spec/bufio/NewWriterSize.lean`, ...), which the
dsverify kits write through over a `net.Conn` (`Net/Proof/net/ConnIo.lean`). The writer-side
counterpart of Perennial's `io.readerOk` (`Perennial/Proof/io/Reader.lean`).

* `io.writerOk wi J Q Ew` (persistent): `wi.Write(p)`, from the state `J out` (`out` the bytes it has
  accepted so far) and the permission `□ Q (out ++ xs)` for `p`'s bytes `xs`, accepts a prefix
  `xs.take k` of them and leaves `J (out ++ xs.take k)`, returning `n = k`, `k ≤ len(p)`, and an error,
  `nil` only when all of `p` was accepted (`io.Writer`'s contract, `io/io.go`: "Write must return a
  non-nil error if it returns n < len(p)"); a non-`nil` error comes with the evidence `Ew` gives of
  it (persistently). `p` is only read (any fraction). `Q`, the client's predicate of what the stream may hold
  (a connection's protocol, ...), is closed under prefixes (`io.prefixClosed`): a writer may accept
  any prefix of what it was given, and `*bufio.Writer` passes on prefixes of its buffer.

`io.writerStream` (`Proof/io/WriterStream.lean`, the WAL's `*os.File`) is the all-or-broken variant:
a failed write leaves the writer's own predicate `B`, not a prefix of the bytes.
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

/-- `Q` holds of every prefix of a stream it holds of persistently (persistent). -/
def io.prefixClosed (Q : List w8 → IProp GF) : IProp GF :=
  iprop(□ (∀ (x y : List w8), □ Q (x ++ y) -∗ Q x))

instance io.prefixClosed_persistent (Q : List w8 → IProp GF) :
    Persistent (io.prefixClosed (GF := GF) Q) := by
  unfold io.prefixClosed; infer_instance

/-- An error result of a writer: `nil`, or an error with the evidence `Ew` (persistently). -/
def io.werrAt (Ew : GoInterface → IProp GF) (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ □ Ew err)

instance io.werrAt_persistent (Ew : GoInterface → IProp GF) (err : GoInterface) :
    Persistent (io.werrAt Ew err) := by
  unfold io.werrAt; infer_instance

/-- **`wi` writes by the contract `J`, `Q`, `Ew`** (see the file header). -/
def io.writerOk (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF) :
    IProp GF :=
  iprop(io.prefixClosed Q ∗
    □ ∀ (out : List w8) (p : GoSlice) (dq : DFrac) (xs : List w8),
    {{ J out ∗ □ Q (out ++ xs) ∗ p ↦*{dq} xs }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, ⌜n = W64 k ∧ k ≤ xs.length ∧ (err = interface.nil → k = xs.length)⌝ ∗
          p ↦*{dq} xs ∗ J (out ++ xs.take k) ∗ io.werrAt Ew err }})

instance io.writerOk_persistent (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) : Persistent (io.writerOk wi J Q Ew) := by
  unfold io.writerOk; infer_instance

/-- A call of `Write`, with `io.writerOk` kept folded in the caller's context. -/
theorem io.wp_writer_Write (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) (out : List w8) (p : GoSlice) (dq : DFrac) (xs : List w8) :
    {{ io.writerOk wi J Q Ew ∗ J out ∗ □ Q (out ++ xs) ∗ p ↦*{dq} xs }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, ⌜n = W64 k ∧ k ≤ xs.length ∧ (err = interface.nil → k = xs.length)⌝ ∗
          p ↦*{dq} xs ∗ J (out ++ xs.take k) ∗ io.werrAt Ew err }} := by
  iintro %Φ ⟨#Hw, HJ, #HQ, Hp⟩ HΦ
  unfold io.writerOk
  icases Hw with ⟨-, #Hw⟩
  iapply Hw $$ %out %p %dq %xs [HJ Hp] HΦ
  iframe HJ HQ Hp

/-- The writer's permission is closed under prefixes. -/
theorem io.writerOk_prefixClosed (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) : io.writerOk wi J Q Ew ⊢ io.prefixClosed Q := by
  unfold io.writerOk
  iintro ⟨#H, -⟩
  iexact H

end defs

end EtcdGrove
end Perennial
