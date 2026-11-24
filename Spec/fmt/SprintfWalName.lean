/-
`fmt.Sprintf("%016x-%016x.wal", seq, index)` of two `uint64`s (the WAL's `walName`, util.go:117):
Go zero-pads the lowercase hexadecimal to the width (`fmt/format.go`, `fmtInteger` with the `zero`
flag), 16 digits for any `uint64`. Proved (`Proof/fmt/SprintfWalName.lean`) from Perennial's
`fmt.wp_Sprintf_walName` over the real `Sprintf` (real `fmt` stage 1, perennial#671, 2026-11-24);
from 2026-11-13 until then a trust-boundary axiom, beyond Perennial's model of `Sprintf`. WAL leaf
specs; Lean-first.
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

/-- **`fmt.Sprintf("%016x-%016x.wal", seq, index)`** of two `uint64`s returns
`fmt.walNameStr seq index`: each 16 lowercase hexadecimal digits. -/
abbrev fmt.SprintfWalName.spec : Prop :=
  ∀ (s i : w64) (sl : GoSlice) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      sl ↦*{dq} [interface.mkOk go.uint64 #s, interface.mkOk go.uint64 #i] }}
    (App (App (Val (@! _root_.Perennial.fmt.Sprintf)) (Val #(go!"%016x-%016x.wal"))) (Val #sl))
  {{ (r : GoString), RET #r;
      sl ↦*{dq} [interface.mkOk go.uint64 #s, interface.mkOk go.uint64 #i] ∗
      ⌜r = fmt.walNameStr s i⌝ }}

end spec

end EtcdGrove
end Perennial
