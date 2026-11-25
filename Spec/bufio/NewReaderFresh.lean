/-
`bufio.NewReaderSize(rd, size)` and `bufio.NewReader(rd)` (Go 1.27.3 `bufio.go`) for `rd` not a
`*bufio.Reader`, `size` at most 4096: a new reader `r.reset(make([]byte, max(size, 16)), rd)`, in
`Reader.Reset`'s state (`bufio.freshReader`: reading `rd`, nothing buffered, no error), which says
nothing of the stream yet (`bufio.freshReader_own` gives `ownReader` once it is known), as
`bufio.Reader.Reset.spec` gives. For net/http's `newBufioReader`, whose pool path is `Reset` and whose
other path is `NewReader`: `conn.readRequest` takes the reader fresh.
-/
module

public import Proof.bufio.RawReader

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
abbrev bufio.NewReaderSize.specFresh : Prop :=
  ∀ (ri : GoInterfaceOk) (size : w64),
  ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty → sint.Z size ≤ 2 ^ 12 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio }}
    (App (App (Val (@! _root_.Perennial.bufio.NewReaderSize)) (Val #(GoInterface.ok ri)))
      (Val #size))
  {{ (br : Loc), RET #br; bufio.freshReader br (GoInterface.ok ri) }}

/-- See the file header. -/
abbrev bufio.NewReader.specFresh : Prop :=
  ∀ (ri : GoInterfaceOk),
  ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio }}
    (App (Val (@! _root_.Perennial.bufio.NewReader)) (Val #(GoInterface.ok ri)))
  {{ (br : Loc), RET #br; bufio.freshReader br (GoInterface.ok ri) }}

end spec

end EtcdGrove
end Perennial
