/-
Ported from dsverify-lab examples/hraft/proof/KitStd/Spec/io/Copy.lean (241f27e), for hashicorp/raft's
proof (`Dsverify/Proof/github_com/hashicorp/raft/InstallBase.lean`): neither Perennial nor this
repository has a general `io.Copy` spec (`Proof/io/CopyGeneric.lean` is `os.File`'s). Perennial
translates `io.Copy` and `copyBuffer` with their bodies; the proof of these specs is still to
do (the lab's `KitStd.Axiom.io.Copy` assumed them; hraft P4, notes/dsv-hraft.md).
-/
/-
`io.Copy`'s specs: a reader whose dynamic type is not an `io.WriterTo` into a writer whose dynamic type is not an
`io.ReaderFrom` (Go's generic copy loop), and into `io.Discard` (its `ReadFrom`). The reader and the writer are
given by their behaviour as byte streams (`io.streamReader`, `io.streamWriter`): persistent Hoare triples for the
method calls `io.Copy` makes on them (`src.Read(p)`, `dst.Write(p)`), as `sort.Slice'`'s spec takes `less`.
-/
module

public import Perennial.Proof.io

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- **`src` (an `io.Reader` value) reads the byte stream `R` describes** (`R cs`: the bytes still to come are
`cs`), given `eof` (the value of `io.EOF`): a call `src.Read(p)` on a slice `p` of `buf.length > 0` bytes returns
`(n, err)` with `0 ≤ n`, having moved the stream's first `n` bytes (no more than `p` holds or the stream has) into
`p`'s first `n` elements and left the rest of `p` as it was; `err` is any error, but `io.EOF` only once the
stream is exhausted (after this call nothing is left). A reader that returns bytes and `io.EOF` together, or
`(0, nil)`, fits; one that returns `io.EOF` with bytes left does not. -/
def io.streamReader (src : GoInterface) (R : List w8 → IProp GF) (eof : GoInterface) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (buf cs : List w8), ⌜0 < buf.length⌝ -∗
    {{ R cs ∗ p ↦* buf }}
      (App (App (Val (GoInstruction (MethodResolve io.Reader.ty go!"Read"))) (Val #src)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ buf.length ∧ sint.nat n ≤ cs.length ∧
          (err = eof → sint.nat n = cs.length)⌝ ∗
        p ↦* (cs.take (sint.nat n) ++ buf.drop (sint.nat n)) ∗ R (cs.drop (sint.nat n)) }})

/-- **`dst` (an `io.Writer` value) appends to the byte stream `W` describes** (`W ws`: the bytes written so far
are `ws`): a call `dst.Write(p)`, with `p` holding `c` (any fraction of it), returns `(n, err)` with
`0 ≤ n ≤ c.length`, having appended `c`'s first `n` bytes, and leaves `p` as it was (it does not keep it, as
`io.Writer`'s contract asks). -/
def io.streamWriter (dst : GoInterface) (W : List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (c ws : List w8) (dq : DFrac),
    {{ W ws ∗ p ↦*{dq} c }}
      (App (App (Val (GoInstruction (MethodResolve io.Writer.ty go!"Write"))) (Val #dst)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ c.length⌝ ∗ W (ws ++ c.take (sint.nat n)) ∗ p ↦*{dq} c }})

open io

/-- `io.Copy(dst, src)` for a reader `src` (dynamic type `ts`, not an `io.WriterTo`) of the stream `bs` and a
writer `dst` (dynamic type `td`, not an `io.ReaderFrom`): it returns `(written, err)`, having read the stream's
first `kr` bytes and written its first `kw` bytes (`kw ≤ kr`; `written = kw`); `err` is nil only if the whole
stream was read and written (`kr = kw = bs.length`). -/
abbrev io.Copy.spec : Prop :=
  ∀ (td ts : go.GoType) (vd vs : val) (R W : List w8 → IProp GF) (bs ws : List w8) (eof : GoInterface),
  go.typeSetContains ts WriterTo.ty = false →
  go.typeSetContains td ReaderFrom.ty = false →
  bs.length < 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr EOF ↦□ eof ∗ R bs ∗ W ws ∗
        streamReader (interface.mkOk ts vs) R eof ∗ streamWriter (interface.mkOk td vd) W }}
      (App (App (Val (@! Copy)) (Val #(interface.mkOk td vd))) (Val #(interface.mkOk ts vs)))
    {{ (written : w64) (err : GoInterface), RET (PairV #written #err);
        ∃ kr kw : Nat, ⌜kw ≤ kr ∧ kr ≤ bs.length ∧ sint.Z written = kw ∧
          (err = interface.nil → kr = bs.length ∧ kw = bs.length)⌝ ∗
        R (bs.drop kr) ∗ W (ws ++ bs.take kw) }}

/-- `io.Copy(io.Discard, src)` (the writer is the value `w` that `io.Discard` holds) for a reader `src` (dynamic
type `ts`, not an `io.WriterTo`) of the stream `bs`: it returns `(n, err)`, having read the stream's first `n`
bytes; `err` is nil only if it read them all (it reads until `io.EOF` or another error). -/
abbrev io.Copy_Discard.spec : Prop :=
  ∀ (w : GoInterface) (ts : go.GoType) (vs : val) (R : List w8 → IProp GF) (bs : List w8) (eof : GoInterface),
  go.typeSetContains ts WriterTo.ty = false →
  bs.length < 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr Discard ↦□ w ∗ globalAddr EOF ↦□ eof ∗ R bs ∗
        streamReader (interface.mkOk ts vs) R eof }}
      (App (App (Val (@! Copy)) (Val #w)) (Val #(interface.mkOk ts vs)))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, ⌜k ≤ bs.length ∧ sint.Z n = k ∧ (err = interface.nil → k = bs.length)⌝ ∗ R (bs.drop k) }}

end spec

end Perennial
