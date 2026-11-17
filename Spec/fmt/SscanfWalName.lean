/-
`fmt.Sscanf(str, "%016x-%016x.wal", &seq, &index)` for `uint64` variables (the WAL's
`parseWALName`, util.go:112): the trust boundary (Perennial translates `fmt` names-only and has no
scanner; `Proof/fmt/SscanfWalName.lean`), as `fmt.Sscanf.spec` is for `"%d"`. The model,
`fmt.scanWalName` (`Proof/fmt/WalName.lean`, which says what it accepts that `walName` never
writes), is Go 1.27's `fmt/scan.go` on this format. WAL leaf specs, 2026-11-13; Lean-first.
-/
module

public import Proof.fmt.WalName
public import Perennial.Proof.fmt

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
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Sscanf(str, "%016x-%016x.wal", &seq, &index)`** for `uint64` variables (the arguments'
slice `[&seq, &index]` as `any`s): returns a count and an error, and leaves some values in the
variables (Go stores each number as it scans it, so a failed scan may leave the first set). Where
`fmt.scanWalName str` is `.ok a b`, the error is `nil` and the variables hold `a` and `b`; where
it is `.err`, the error is not `nil`; where it is `.unknown` (a space where Go skips spaces), the
spec says nothing more. -/
abbrev fmt.SscanfWalName.spec : Prop :=
  ∀ (str : GoString) (sl : GoSlice) (dq : DFrac) (p q : Loc) (a0 b0 : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      sl ↦*{dq} [interface.mkOk (go.GoType.PointerType go.uint64) #p,
        interface.mkOk (go.GoType.PointerType go.uint64) #q] ∗ p ↦ a0 ∗ q ↦ b0 }}
    (App (App (App (Val (@! _root_.Perennial.fmt.Sscanf)) (Val #str))
      (Val #(go!"%016x-%016x.wal"))) (Val #sl))
  {{ (cnt : w64) (err : GoInterface), RET (PairV #cnt #err);
      sl ↦*{dq} [interface.mkOk (go.GoType.PointerType go.uint64) #p,
        interface.mkOk (go.GoType.PointerType go.uint64) #q] ∗
      ∃ a b : w64, p ↦ a ∗ q ↦ b ∗
      ⌜(∀ x y, fmt.scanWalName str = .ok x y → err = GoInterface.nil ∧ a = x ∧ b = y) ∧
        (fmt.scanWalName str = .err → err ≠ GoInterface.nil)⌝ }}

end spec

end EtcdGrove
end Perennial
