/-
`fmt.Sprintf`: the trust boundary, for arguments that are not all of predeclared basic types
(as `fmt.Errorf` and `fmt.Printf`, `Spec/fmt/Errorf.lean`, whose `fmt.argsOk` it shares; the
snapshot handler's error messages, `%v` of an error; rafthttp stage 7e, the user's choice).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.Errorf
public import Perennial.Spec.fmt.Sprintf

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

/-- **`fmt.Sprintf(format, args...)`**: Perennial's spec of the real `Sprintf` (real `fmt` stage 1,
perennial#671): the format made of pieces in the verified subset, each argument an `fmt.isArg`
(those Go formats by their `Error()`/`String()` with the method's spec), the output `fmt.Out`.
Until 2026-11-24 any format, arguments `fmt.argsOk` under its verbs, some string (over the
trusted model of `Sprintf`). -/
abbrev fmt.SprintfArgs.spec : Prop := _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG)

end spec

end EtcdGrove
end Perennial
