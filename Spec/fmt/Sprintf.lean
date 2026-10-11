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
it only to build a log line. The postcondition is *some* string: nothing reads what it
says.

It asks only that an argument of dynamic type `string` hold a string
(`fmt.StringArgsWf`, which Perennial's model, formatting `%s`, needs); `newRaft` passes only
`uint64`s. -/
abbrev fmt.Sprintf.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args ↦*{dq} xs ∗
      ⌜_root_.Perennial.fmt.StringArgsWf xs⌝ }}
    (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
  {{ (s : GoString), RET #s; args ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
