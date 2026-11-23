/-
`(*bufio.Writer).Write(p)` (Go 1.27.3 `bufio.go`) over a writer by the `io.Writer` contract
(`bufio.ownBufWriter`), with `□ Q (sent ++ pend ++ ps)` for `p`'s bytes `ps`: accepts the first
`k` bytes of `p` (all of them when it returns `nil`; none with a sticky error); a prefix of the
accepted stream has been sent (`sent'`), the rest is buffered (`pend'`); the error returned is the
writer's sticky error after. `p` is only read. Proved in `Proof/bufio/Writer__Write.lean`.
dsv-bufio, 2026-11-23 (#24).
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
abbrev bufio.Writer.Write.spec : Prop :=
  ∀ (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF)
    (sent pend : List w8) (err : GoInterface) (p : GoSlice) (dq : DFrac) (ps : List w8),
  {{ bufio.ownBufWriter bw wi J Q Ew sent pend err ∗ □ Q (sent ++ pend ++ ps) ∗ p ↦*{dq} ps }}
    (App (Val (bw @!! go.GoType.PointerType _root_.Perennial.bufio.Writer.ty @!! go!"Write")) (Val #p))
  {{ (nn : w64) (e : GoInterface), RET (PairV #nn #e); ∃ (k : Nat) (sent' pend' : List w8),
      ⌜nn = W64 k ∧ k ≤ ps.length ∧ sent' ++ pend' = sent ++ pend ++ ps.take k ∧
        sent <+: sent' ∧ (e = interface.nil → k = ps.length) ∧
        (err ≠ interface.nil → e = err ∧ k = 0)⌝ ∗
      p ↦*{dq} ps ∗ bufio.ownBufWriter bw wi J Q Ew sent' pend' e }}

end spec

end EtcdGrove
end Perennial
