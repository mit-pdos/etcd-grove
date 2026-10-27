/-
`fmt.Sprintf` with `types.ID` arguments: the trust boundary, for rafthttp's
`peerStatus.deactivate`, `Sprintf("failed to %s %s on %s (%s)", action, s.id, source, reason)`
(rafthttp stage 4d). Perennial's `fmt.wp_Sprintf` admits arguments of predeclared basic types only
(`fmt.ArgsWf`); a `types.ID` is a named type with a `String` method, which Go calls. A spec of its
own (as `fmt.SprintfNamed`), so that `Sprintf`'s other callers do not rest on it. Lean-first.
-/
module

public import Perennial.Proof.fmt
public import Code.go_etcd_io.etcd.client.pkg.v3.types

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- An argument of `Sprintf` whose formatting Go does by itself or by `types.ID.String`: `nil`, a
value of a predeclared basic type (`fmt.ArgWf`), or a `types.ID`, whose `String` is
`strconv.FormatUint(uint64(i), 16)` (`client/pkg/types/id.go`): it reads no memory and cannot
panic. -/
def fmt.SprintfIDArgOk : GoInterface → Prop
  | .nil => True
  | .ok ii => _root_.Perennial.fmt.ArgWf ii ∨
      ii.ty = go_etcd_io.etcd.client.pkg.v3.types.ID.ty

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- `fmt.Sprintf(format, args...)` with every argument `fmt.SprintfIDArgOk` returns a string
`s` with `fmt.SprintfOut format xs s`, as Perennial's `fmt.wp_Sprintf` states it (a `types.ID`
argument is formatted by a directive the model does not interpret: the rest of the output is
arbitrary), and gives the arguments' slice back. At the trust boundary
(`Proof/fmt/SprintfID.lean`). -/
abbrev fmt.SprintfID.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args ↦*{dq} xs ∗
        ⌜∀ a ∈ xs, fmt.SprintfIDArgOk a⌝ }}
      (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
    {{ (s : GoString), RET #s; args ↦*{dq} xs ∗ ⌜_root_.Perennial.fmt.SprintfOut format xs s⌝ }}

end spec

end EtcdGrove
end Perennial
