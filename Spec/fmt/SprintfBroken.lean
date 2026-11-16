/-
`fmt.Sprintf("%s.broken.%v", dir, s)` of two strings (the WAL's `cleanupWAL`, S/wal.go: the broken
directory's name, `s` the timestamp `time.Now().Format(...)` returns): **a hypothesis** of
`cleanupWAL`'s proof, not proved here and not an axiom; pending the user (plan §10). **Beyond
Perennial's model of `Sprintf`** (`Perennial/Proof/fmt/Base.lean`, `SprintfOut`), which formats `%s`
of a string but `%v` only of an integer: from `%v` of a string on its output is arbitrary. Go's `%v`
of a string prints it as `%s` does (`fmt/print.go`, `printArg`'s `case string: p.fmtString(f, verb)`,
`fmtString`'s `case 'v'` without `#`: `fmtS`). The proposed Perennial change, the model reading `%v`
of a string as `%s`, is `notes/perennial-changes.md`, "`Sprintf`'s `%v` of a string". Lean-first.
-/
module

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

/-- **`fmt.Sprintf("%s.broken.%v", d, s)`** of two strings returns `d ++ ".broken." ++ s`. -/
abbrev fmt.SprintfBroken.spec : Prop :=
  ∀ (d s : GoString) (sl : GoSlice) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      sl ↦*{dq} [interface.mkOk go.string #d, interface.mkOk go.string #s] }}
    (App (App (Val (@! _root_.Perennial.fmt.Sprintf)) (Val #(go!"%s.broken.%v"))) (Val #sl))
  {{ (r : GoString), RET #r;
      sl ↦*{dq} [interface.mkOk go.string #d, interface.mkOk go.string #s] ∗
      ⌜r = d ++ go!".broken." ++ s⌝ }}

end spec

end EtcdGrove
end Perennial
