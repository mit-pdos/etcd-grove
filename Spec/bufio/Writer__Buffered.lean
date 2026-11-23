/-
`(*bufio.Writer).Buffered()` (Go 1.27.3 `bufio.go`: `b.n`) of a writer by the `io.Writer` contract
(`bufio.ownBufWriter`, its buffer of `sz` bytes holding `pend`): the number of buffered bytes, `pend.length`. Proved in
`Proof/bufio/Writer__Buffered.lean`. dsv-bufio, review W2 on #24.
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
abbrev bufio.Writer.Buffered.spec : Prop :=
  ∀ (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF)
    (sz : Nat) (sent pend : List w8) (err : GoInterface),
  {{ bufio.ownBufWriter bw wi J Q Ew sz sent pend err }}
    (App (Val (bw @!! go.GoType.PointerType _root_.Perennial.bufio.Writer.ty @!! go!"Buffered")) (Val #()))
  {{ (n : w64), RET #n; ⌜sint.Z n = pend.length⌝ ∗ bufio.ownBufWriter bw wi J Q Ew sz sent pend err }}

end spec

end EtcdGrove
end Perennial
