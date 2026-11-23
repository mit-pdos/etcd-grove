/-
`(*bufio.Writer).Flush()` (Go 1.27.3 `bufio.go`) over a writer by the `io.Writer` contract
(`bufio.ownBufWriter`): sends a prefix `pend.take k` of the buffered bytes, all of them when it
returns `nil`; with a sticky error, nothing, and that error. The error returned is the writer's
sticky error after (`io.werrAt Ew`). Proved in `Proof/bufio/Writer__Flush.lean`. dsv-bufio,
2026-11-23 (#24).
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
abbrev bufio.Writer.Flush.spec : Prop :=
  ∀ (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF)
    (sent pend : List w8) (err : GoInterface),
  {{ bufio.ownBufWriter bw wi J Q Ew sent pend err }}
    (App (Val (bw @!! go.GoType.PointerType _root_.Perennial.bufio.Writer.ty @!! go!"Flush")) (Val #()))
  {{ (e : GoInterface), RET #e; ∃ k : Nat,
      ⌜k ≤ pend.length ∧ (e = interface.nil → k = pend.length) ∧
        (err ≠ interface.nil → e = err ∧ k = 0)⌝ ∗
      bufio.ownBufWriter bw wi J Q Ew (sent ++ pend.take k) (pend.drop k) e }}

end spec

end EtcdGrove
end Perennial
