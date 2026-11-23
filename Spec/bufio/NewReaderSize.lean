/-
`bufio.NewReaderSize(rd, size)` (Go 1.27.3 `bufio.go`) over a reader `rd` by Perennial's
`io.Reader` contract (`io.readerOk ri Pre S E`) that is not already a `*bufio.Reader` (which it
would return as is): a fresh reader with a buffer of `max(size, 16)` bytes, nothing returned or
buffered (`bufio.ownBufReader`, `Proof/bufio/Own.lean`); every read of at most that many bytes
must meet `Pre`. Proved in `Proof/bufio/NewReaderSize.lean`. dsv-bufio, 2026-11-23 (#24).
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
abbrev bufio.NewReaderSize.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (size : w64),
  ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty →
  bufio.preUpTo Pre (max (sint.Z size) 16).toNat →
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ _root_.Perennial.io.readerOk ri Pre S E ∗ S R }}
    (App (App (Val (@! _root_.Perennial.bufio.NewReaderSize)) (Val #(GoInterface.ok ri)))
      (Val #size))
  {{ (br : Loc), RET #br; bufio.ownBufReader br ri Pre S E R }}

end spec

end EtcdGrove
end Perennial
