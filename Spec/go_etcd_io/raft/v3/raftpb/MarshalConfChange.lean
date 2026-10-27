/-
`MarshalConfChange` (`raftpb/confchange.go:35`). Port of the old spec to raft v3.7 (a
`ConfChangeI` holds a pointer; `proto.Marshal` instead of gogoproto's generated `Marshal`; stage
R1).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `MarshalConfChange(c)` for `c` holding `o` (`ownConfChangeI`: `nil`, a `*ConfChange` or a
`*ConfChangeV2`): the entry type `confChangeEntryType o`, a fresh slice of bytes carrying the change
(`MarshalsConfChange`: bytes that decode back to it; the `nil` slice for `nil`) and a `nil` error
(`proto.Marshal` does not fail on these messages, `proto.MarshalConfChange.spec`). -/
abbrev raftpb.MarshalConfChange.spec : Prop :=
  ∀ (c : GoInterface) (o : Option ConfChangeIM) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownConfChangeI c dq o }}
    (App (Val #(functions raftpb.MarshalConfChange [])) (Val #c))
  {{ (data : GoSlice) (bs : List w8),
      RET (PairV (PairV #(confChangeEntryType o) #data) #interface.nil);
      ownConfChangeI c dq o ∗ data ↦* bs ∗ ⌜MarshalsConfChange o bs⌝ }}

end spec

end EtcdGrove
end Perennial
