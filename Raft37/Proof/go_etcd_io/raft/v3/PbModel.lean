/-
The raftpb values as the protocol model sees them (raft v3.7 retarget, stage R0, provisional:
`notes/raft-retarget-plan.md`, "Design", D1). Until the retarget the protocol model (`Plog`,
`CCModel`, `Protocol/*`) used the Goose value of gogoproto's `raftpb.Entry` (a struct of four
plain fields) as its entry, and stored the pending read-index requests as Goose
`raftpb.Message` values (reading their `From'`).
In raft v3.7 (protobuf-go v2) `raftpb.Entry` is a struct of pointers (`Term`, `Index`,
`Type`) and protobuf runtime state, only ever handled through a `*pb.Entry`, so it is not a
pure value any more. `EntryM` is the record the old Goose value was, field for field
(the same names, so the model's text is unchanged but for the type's name): what a
`*pb.Entry` holds, read through its getters (`GetTerm`, `GetIndex`, `GetType`,
`GetData`). The bytes of `Data'` are owned apart, as before. `MessageM` is likewise what a
`*pb.Message`'s scalar getters return, named as gogoproto's fields were (the model reads
`From'` of a pending read-index request); its references (`Entries`, `Snapshot`,
`Context`, `Responses`) are not in it. `ConfChangeSingleM` is a `*pb.ConfChangeSingle`'s
`GetType()` and `GetNodeId()`, the model of one conf change (`CCModel`, `InvConfchange`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Raft37.Code.go_etcd_io.raft.v3

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- A log entry as the model sees it: what `GetTerm()`, `GetIndex()`, `GetType()`,
`GetData()` of a `*pb.Entry` return (a nil field reads as zero). -/
structure EntryM [FfiSyntax] where
  mk ::
  Term' : w64
  Index' : w64
  Type' : raftpb.EntryType
  Data' : GoSlice

instance EntryM.zero_val [FfiSyntax] : ZeroVal EntryM :=
  ⟨EntryM.mk zeroValDef zeroValDef zeroValDef zeroValDef⟩

/-- A message's scalar fields as the model sees them: what `GetType()`, `GetTo()`, ...,
`GetRejectHint()` of a `*pb.Message` return. -/
structure MessageM [FfiSyntax] where
  mk ::
  Type' : raftpb.MessageType
  To' : w64
  From' : w64
  Term' : w64
  LogTerm' : w64
  Index' : w64
  Commit' : w64
  Vote' : w64
  Reject' : Bool
  RejectHint' : w64

instance MessageM.zero_val [FfiSyntax] : ZeroVal MessageM :=
  ⟨MessageM.mk zeroValDef zeroValDef zeroValDef zeroValDef zeroValDef zeroValDef zeroValDef
    zeroValDef zeroValDef zeroValDef⟩

/-- One conf change as the model sees it: `GetType()`, `GetNodeId()` of a
`*pb.ConfChangeSingle`. -/
structure ConfChangeSingleM [FfiSyntax] where
  mk ::
  Type' : raftpb.ConfChangeType
  NodeId' : w64

instance ConfChangeSingleM.zero_val [FfiSyntax] : ZeroVal ConfChangeSingleM :=
  ⟨ConfChangeSingleM.mk zeroValDef zeroValDef⟩

end EtcdGrove
end Perennial
