/-
`binary.Read(r, binary.LittleEndian, p)` into an `*int64`: the trust boundary (names-only in
Perennial; `Proof/encoding/binary/ReadInt64LE.lean`), stated over `io.ReadFull` of `r`, as
`binary.ReadUint64` (`Spec/encoding/binary/ReadUint64.lean`) is for the big-endian `*uint64`. The
WAL's `readInt64` (decoder.go:227-231). WAL leaf specs, 2026-11-13; Lean-first.
-/
module

public import Perennial.Proof.encoding.binary.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **`binary.LittleEndian` as a `binary.ByteOrder`**: the global loaded (a struct without
fields: its zero value) and converted to the interface. -/
abbrev littleEndianOrder : GoInterface :=
  interface.mkOk encoding.binary.littleEndian.ty #(zero_val encoding.binary.littleEndian)

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `binary.Read(r, binary.LittleEndian, p)` into an `*int64` makes one `io.ReadFull(r, bs)` of a
fresh eight-byte slice; if it fails, returns its error and leaves `*p`, else sets `*p` to the
bytes' little-endian value and returns `nil` (Go 1.27 `binary.go`, `Read`'s fast path:
`intDataSize` is 8, `io.ReadFull`, `decodeFast`'s `case *int64: *data =
int64(order.Uint64(bs))`). Stated over that call's triple, `P` to `Q` of the bytes `ys` read,
which are all eight unless the error is non-nil. -/
abbrev binary.ReadInt64LE.spec : Prop :=
  ∀ (r : GoInterface) (p : Loc) (x : w64) (P : IProp GF)
    (Q : List w8 → w64 → GoInterface → IProp GF),
    ⊢ (□ ∀ (sl : GoSlice) (xs : List w8), {{ sl ↦* xs ∗ ⌜xs.length = 8⌝ ∗ P }}
        (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #r)) (Val #sl))
        {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
            ∃ ys, sl ↦* (ys ++ xs.drop ys.length) ∗
              ⌜ys.length ≤ 8 ∧ (err = GoInterface.nil → ys.length = 8)⌝ ∗ Q ys n err }}) -∗
      {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ P ∗ p ↦ x }}
        (App (App (App (Val (@! _root_.Perennial.encoding.binary.Read)) (Val #r))
          (Val #littleEndianOrder))
          (Val #(interface.mkOk (go.GoType.PointerType go.int64) #p)))
      {{ (err : GoInterface), RET #err;
          ∃ ys n, Q ys n err ∗
            (⌜err = GoInterface.nil ∧ ys.length = 8⌝ ∗ p ↦ leToU64 ys ∨
             ⌜err ≠ GoInterface.nil⌝ ∗ p ↦ x) }}

end spec

end EtcdGrove
end Perennial
