/-
`(*bufio.Writer).WriteByte(c)` (Go 1.27.3 `bufio.go`) over a writer by the `io.Writer` contract
(`bufio.ownBufWriter`), with `□ Q (sent ++ pend ++ [c])` when the writer is healthy
(`⌜err = nil⌝ -∗ …`: with a sticky error Go returns it at once, `bufio.go:691-692`): accepts `c`
when it returns `nil`, nothing otherwise (a full buffer is flushed first, which may send a prefix
of it); the error returned is the writer's sticky error after. With a sticky error it changes
nothing and returns it; with room in the buffer (`pend.length + 1 ≤ sz`) a healthy writer sends
nothing and returns `nil`. Proved in `Proof/bufio/Writer__WriteByte.lean`. dsv-bufio, 2026-11-23
(#24); revised after the review (W1, W2, W3).
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
abbrev bufio.Writer.WriteByte.spec : Prop :=
  ∀ (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF)
    (sz : Nat) (sent pend : List w8) (err : GoInterface) (c : w8),
  {{ bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗
      (⌜err = interface.nil⌝ -∗ □ Q (sent ++ pend ++ [c])) }}
    (App (Val (bw @!! go.GoType.PointerType _root_.Perennial.bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
  {{ (e : GoInterface), RET #e; ∃ sent' pend' : List w8,
      ⌜sent <+: sent' ∧ (e = interface.nil → sent' ++ pend' = sent ++ pend ++ [c]) ∧
        (e ≠ interface.nil → sent' ++ pend' = sent ++ pend) ∧
        (err ≠ interface.nil → e = err ∧ sent' = sent ∧ pend' = pend) ∧
        (err = interface.nil ∧ pend.length + 1 ≤ sz → e = interface.nil ∧ sent' = sent)⌝ ∗
      bufio.ownBufWriter bw wi J Q Ew sz sent' pend' e }}

end spec

end EtcdGrove
end Perennial
