/- `DescribeConfChange` (`util.go`, raft v3.7), Lean-first (2026-10-16, stage R4): what
`stepLeader`'s conf-change refusal log line calls on the decoded conf change. -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `DescribeConfChange(cc)` formats a conf change (`cc.AsV2()`, its transition, changes and
context, through `fmt.Fprintf` into a `strings.Builder`) into a log string. Of the string
nothing is said (raft only logs it); the conf change, a `*pb.ConfChange` or a
`*pb.ConfChangeV2` behind the `ConfChangeI` interface (what `stepLeader` decodes with
`proto.Unmarshal`), is read and given back. -/
abbrev DescribeConfChange.spec : Prop :=
  (∀ (p : Loc) (dq : DFrac) (m : CCV1M),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownCCV1 p dq m }}
      (App (Val #(functions DescribeConfChange []))
        (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p)))
    {{ (str : GoString), RET #str; ownCCV1 p dq m }}) ∧
  (∀ (p : Loc) (dq : DFrac) (m : CCV2M),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownCCV2 p dq m }}
      (App (Val #(functions DescribeConfChange []))
        (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #p)))
    {{ (str : GoString), RET #str; ownCCV2 p dq m }})

end spec

end EtcdGrove
end Perennial
