/-
`MarshalConfChange` (`raftpb/confchange.go:35`). Port of the old spec to raft v3.7 (a
`ConfChangeI` holds a pointer; `proto.Marshal` instead of gogoproto's generated `Marshal`; stage
R1).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `MarshalConfChange(c)` for `c` holding `o` (`ownCCI`: `nil`, a `*ConfChange` or a
`*ConfChangeV2`): the entry type `ccEntryType o`, a fresh slice of bytes carrying the change
(`CCData`: bytes that decode back to it; the `nil` slice for `nil`) and a `nil` error
(`proto.Marshal` does not fail on these messages, `proto.MarshalConfChange.spec`). -/
abbrev raftpb.MarshalConfChange.spec : Prop :=
  ∀ (c : GoInterface) (o : Option CCMsg) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownCCI c dq o }}
    (App (Val #(functions raftpb.MarshalConfChange [])) (Val #c))
  {{ (data : GoSlice) (bs : List w8),
      RET (PairV (PairV #(ccEntryType o) #data) #interface.nil);
      ownCCI c dq o ∗ data ↦* bs ∗ ⌜CCData o bs⌝ }}

end spec

end EtcdGrove
end Perennial
