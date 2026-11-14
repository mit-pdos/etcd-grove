/-
`bufio.NewReader(rd)` (Go 1.27 `bufio.go`, the part's translation): for a reader that is not
already a `*bufio.Reader` (`NewReaderSize` would return that one itself), a fresh reader with a
4096-byte buffer and nothing buffered. Proved in `LinuxFs/Proof/bufio/NewReader.lean`. WAL leaf
specs, 2026-11-13 (`fileutil.NewFileBufReader`); Lean-first.
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

/-- `NewReader(rd)`, `rd` holding `ri` (not a `*bufio.Reader`), from the stream state `S r`:
a reader that has delivered `r`. -/
abbrev bufio.NewReader.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r : List w8),
  ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ S r }}
    (App (Val (@! _root_.Perennial.bufio.NewReader)) (Val #(GoInterface.ok ri)))
  {{ (b : Loc), RET #b; bufio.ownReader b ri S E r }}

end spec

end EtcdGrove
end Perennial
