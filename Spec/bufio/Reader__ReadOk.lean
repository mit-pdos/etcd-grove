/-
`(*bufio.Reader).Read(p)` (Go 1.27.3 `bufio.go`) over a reader by Perennial's `io.Reader`
contract (`bufio.ownBufReader`): the next bytes `ys` of the stream (at most `len(p)`) in the front
of `p`, the rest of `p` unchanged, and `nil` or an error with its evidence at `R ++ ys`
(`bufio.errE E`); bytes and an error may come together (as the underlying reader's). A read of
`p` directly from the underlying reader (`len(p)` at least the buffer's size) must meet `Pre`.
The post is `io.readerOk`'s, for the reader `br` with state `bufio.ownBufReader br ri Pre S E`
(`Proof/bufio/ReaderLaws.lean`). The generic spec of `Read`; `bufio.Reader.Read.spec`
(`Spec/bufio/Reader__Read.lean`) is the WAL's, over `io.readerStream`. Proved in
`Proof/bufio/Reader__ReadOk.lean`. dsv-bufio, 2026-11-23 (#24).
-/
module

public import Proof.bufio.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
abbrev bufio.Reader.Read.specOk : Prop :=
  ∀ (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (p : GoSlice) (xs : List w8),
  (∀ r, 0 < xs.length → Pre r xs.length) →
  {{ bufio.ownBufReader br ri Pre S E R ∗ p ↦* xs }}
    (App (Val (br @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"Read")) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ bufio.ownBufReader br ri Pre S E (R ++ ys) ∗
        _root_.Perennial.io.errAt (bufio.errE E) (R ++ ys) err ∗
        ⌜_root_.Perennial.io.ptrTyped err⌝ }}

end spec

end EtcdGrove
end Perennial
