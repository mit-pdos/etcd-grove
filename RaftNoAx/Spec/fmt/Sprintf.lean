-- The copy for the part `RaftNoAx/` of `Spec/fmt/Sprintf.lean` (etc/copy-part.py; rerun it, do not edit).
/- Port of election_proof/spec_fmt_Sprintf.v (feb5c73d4). -/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvStorage
public import Proof.fmt.SprintfPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`fmt.Sprintf(format, args...)` of arguments that call no method** (`fmt.PureArgs`: `nil`, a
`bool`, a value of a predeclared integer type, a `string`), the format `fmt.encode ps` in the
verified subset of the real `fmt` (`fmt.Fits`): returns `fmt.render ps args`, the pieces' outputs
in order, and gives the arguments' slice back. `newRaft` formats `uint64`s with `%x` for a log
line; `stepLeader` refuses a conf change only when its `failedCheck` message, a `Sprintf` of a
format beginning with a letter, is non-empty.

Since 2026-11-24 (real `fmt` stage 1, perennial#671) proved from Perennial's spec of the
translated `Sprintf` (`Proof/fmt/Sprintf.lean`). Until then any format, with arguments
`fmt.ArgsWf` and the output `fmt.SprintfOut`, over Perennial's trusted model of `Sprintf`; until
2026-10-13 the postcondition was *some* string. -/
abbrev fmt.Sprintf.spec : Prop :=
  ∀ (format : GoString) (ps : List _root_.Perennial.fmt.Piece) (args : GoSlice)
    (xs : List GoInterface) (pargs : List _root_.Perennial.fmt.Arg) (dq : DFrac),
  format = _root_.Perennial.fmt.encode ps → _root_.Perennial.fmt.Fits ps pargs →
  fmt.PureArgs xs pargs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args ↦*{dq} xs }}
    (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
  {{ (s : GoString), RET #s; args ↦*{dq} xs ∗
      ⌜s = _root_.Perennial.fmt.render ps pargs⌝ }}

end spec

end EtcdGrove
end Perennial
