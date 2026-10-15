/- Port of election_proof/spec_fmt_Sprintf.v (feb5c73d4). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `fmt.Sprintf` is not translated (`fmt`'s printer reaches `reflect`); Perennial
models it (`Perennial/TrustedCode/fmt.lean`) and proves `fmt.wp_Sprintf`. `newRaft` uses
it only to build a log line. Until 2026-10-13 the postcondition was *some* string; since
then it is the model's (`SprintfOut`): `stepLeader` refuses a conf change only when its
`failedCheck` message, a `Sprintf` of a format beginning with a letter, is non-empty.

It asks only that an argument's dynamic type tell the truth about its value for the types
Perennial's model formats (`fmt.ArgsWf`: a `string` holds a string, an integer type an integer);
`newRaft` passes only `uint64`s. -/
abbrev fmt.Sprintf.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args ↦*{dq} xs ∗
      ⌜_root_.Perennial.fmt.ArgsWf xs⌝ }}
    (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
  {{ (s : GoString), RET #s; args ↦*{dq} xs ∗
      -- (2026-10-13) what is printed (`stepLeader`'s conf-change refusal needs a non-empty
      -- message)
      ⌜_root_.Perennial.fmt.SprintfOut format xs s⌝ }}

end spec

end EtcdGrove
end Perennial
