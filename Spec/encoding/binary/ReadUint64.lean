/-
`binary.Read(r, binary.BigEndian, p)` into a `*uint64`: the trust boundary (names-only in
Perennial), stated over `io.ReadFull` of `r`. Lean-first.
-/
module

public import Proof.encoding.binary.Defs

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

/-- `binary.Read(r, binary.BigEndian, p)` into a `*uint64` makes one `io.ReadFull(r, bs)` of a
fresh eight-byte slice; if it fails, returns its error (`*p` as it likes: Go leaves it, the spec
need not say), else sets `*p` to the bytes' big-endian value and returns `nil` (Go 1.27
`binary.go`, `Read`'s fast path: `intDataSize`, `io.ReadFull`, `decodeFast`). Stated over that
call's triple, `P` to `Q` of the bytes `ys` read, which are all eight unless the error is
non-nil. -/
abbrev binary.ReadUint64.spec : Prop :=
  ∀ (r : GoInterface) (p : Loc) (x : w64) (P : IProp GF)
    (Q : List w8 → w64 → GoInterface → IProp GF),
    ⊢ (□ ∀ (sl : GoSlice) (xs : List w8), {{ sl ↦* xs ∗ ⌜xs.length = 8⌝ ∗ P }}
        (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #r)) (Val #sl))
        {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
            ∃ ys, sl ↦* (ys ++ xs.drop ys.length) ∗
              ⌜ys.length ≤ 8 ∧ (err = GoInterface.nil → ys.length = 8)⌝ ∗ Q ys n err }}) -∗
      {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ P ∗ p ↦ x }}
        (App (App (App (Val (@! _root_.Perennial.encoding.binary.Read)) (Val #r))
          (Val #bigEndianOrder))
          (Val #(interface.mkOk (go.GoType.PointerType go.uint64) #p)))
      {{ (err : GoInterface), RET #err;
          ∃ ys n, Q ys n err ∗
            (⌜err = GoInterface.nil ∧ ys.length = 8⌝ ∗ p ↦ beToU64 ys ∨
             ⌜err ≠ GoInterface.nil⌝ ∗ ∃ x' : w64, p ↦ x') }}

end spec

end EtcdGrove
end Perennial
