/-
`(*bufio.Reader).Read(p)` (Go 1.27 `bufio.go`, the part's translation): a buffered reader over a
stream reader is a stream reader of the same bytes and errors (`bufio.ownReader`,
`LinuxFs/Proof/bufio/Defs.lean`). Proved in `LinuxFs/Proof/bufio/Reader__Read.lean`. WAL leaf
specs, 2026-11-13 (the decoder reads through `fileutil.FileBufReader`'s embedded reader);
Lean-first.
-/
module

public import LinuxFs.Proof.bufio.Defs

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

/-- `b.Read(p)`, `b` over the stream reader `ri`: delivers the next bytes `ys` (at most `len(p)`)
into the front of `p`, from the buffer or from `ri`, and returns only an error `ri` returned
there (`io.readerStream`'s triple, for `b`). A refill reads a whole buffer (up to 4 KiB) at
the stream's position, so the underlying stream's states stay 4 KiB below `2^62`. -/
abbrev bufio.Reader.Read.spec : Prop :=
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → Prop)
    (r : List w8) (p : GoSlice) (xs : List w8),
  ⊢ io.readerStream ri S E -∗ (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) -∗
    {{ ⌜r.length + xs.length < 2 ^ 62⌝ ∗ bufio.ownReader b ri S E r ∗ p ↦* xs }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"Read"))
        (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
          (err ≠ GoInterface.nil → E (r ++ ys) err)⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ bufio.ownReader b ri S E (r ++ ys) }}

end spec

end EtcdGrove
end Perennial
