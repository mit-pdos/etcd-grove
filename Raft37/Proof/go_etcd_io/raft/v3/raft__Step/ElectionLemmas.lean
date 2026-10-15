/- The election branches' own helpers for `Step`'s proof (raft v3.7 retarget, stage R4 phase 3,
group G4a).

`raft.Step.Postulates` (`Base.lean`) bundles the callee specs of `raft.go`; since v3.7 `Step`
also reads the message through its protobuf getters (`m.GetTerm()`, ...) and builds responses
with `MessageType.Enum()`, whose specs (R1, `Raft37/Spec/.../raftpb/`) are bundled here as
`raft.Step.PbPostulates`, which the election branch lemmas take beside `raft.Step.Postulates`.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.raft__Step.Base
public import Raft37.Proof.go_etcd_io.raft.v3.InvPbMsg
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetContext
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section base
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The protobuf specs `Step`'s election branches use (stage R4): the message getters and
`MessageType.Enum`. -/
structure raft.Step.PbPostulates : Prop where
  GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)
  GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG)
  GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)
  GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG)
  GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG)
  GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG)
  GetContext : raftpb.Message.GetContext.spec (GF := GF) (hG := hG)
  Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)

/-- A message's pointer is not `nil` (kept). -/
theorem msgPtsC_nn (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢ ⌜l ≠ null⌝ ∗ msgPtsC l dq dqe cap ms := by
  iintro H
  ihave %Hnn : ⌜l ≠ null⌝ $$ [H]
  · iunfold msgPtsC at H
    iNamed H
    ipureintro; exact Hnn
  iframe H
  ipureintro; exact Hnn

end base

end EtcdGrove
end Perennial
