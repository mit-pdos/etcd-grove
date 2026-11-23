/-
`bufio.NewReader(rd)` (Go 1.27 `bufio.go`) for the WAL: for a stream reader (`io.readerStream ri
S E`, its states' delivered bytes `2^12` below `2^62`) that is not already a `*bufio.Reader`
(`NewReaderSize` would return that one itself), a fresh reader with a 4096-byte buffer and nothing
buffered (`bufio.ownReader`). Proved in `Proof/bufio/NewReader.lean` from the generic
`bufio.NewReaderSize.specE` (`Proof/bufio/OwnReaderE.lean`; review R1 on #24: one proof per
function). WAL leaf specs, 2026-11-13 (`fileutil.NewFileBufReader`); the reader's contract and bound
added 2026-11-23 (dsv-bufio). Lean-first.
-/
module

public import Proof.bufio.Defs

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

/-- `NewReader(rd)`, `rd` holding the stream reader `ri` (not a `*bufio.Reader`), from the stream
state `S r`: a reader that has delivered `r`. -/
abbrev bufio.NewReader.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r : List w8),
  ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ io.readerStream ri S E ∗
      (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) ∗ S r }}
    (App (Val (@! _root_.Perennial.bufio.NewReader)) (Val #(GoInterface.ok ri)))
  {{ (b : Loc), RET #b; bufio.ownReader b ri S E r }}

end spec

end EtcdGrove
end Perennial
