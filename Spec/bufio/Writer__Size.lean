/-
`(*bufio.Writer).Size()` (Go 1.27.3 `bufio.go`: `len(b.buf)`) of a writer by the `io.Writer` contract
(`bufio.ownBufWriter`, its buffer of `sz` bytes holding `pend`): the buffer's size, `sz`. Proved in
`Proof/bufio/Writer__Size.lean`. dsv-bufio, review W2 on #24.
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
abbrev bufio.Writer.Size.spec : Prop :=
  ∀ (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF)
    (sz : Nat) (sent pend : List w8) (err : GoInterface),
  {{ bufio.ownBufWriter bw wi J Q Ew sz sent pend err }}
    (App (Val (bw @!! go.GoType.PointerType _root_.Perennial.bufio.Writer.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; ⌜sint.Z n = sz⌝ ∗ bufio.ownBufWriter bw wi J Q Ew sz sent pend err }}

end spec

end EtcdGrove
end Perennial
