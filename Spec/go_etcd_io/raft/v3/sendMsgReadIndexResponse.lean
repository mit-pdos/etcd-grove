/- Lean-first (no Rocq counterpart; 2026-10-12, read-index).

## `sendMsgReadIndexResponse(r, m)` (raft.go:2134)

    switch r.readOnly.option {
    case ReadOnlySafe:
        r.readOnly.addRequest(r.raftLog.committed, m)
        r.readOnly.recvAck(r.id, r.readOnly.heartbeatCtx())
        r.bcastHeartbeat()
    case ReadOnlyLeaseBased: ...
    }

The option is `ReadOnlySafe` (`ownReadOnly`). The request is queued, read at the commit
index (`readonlyArrive`: queued, then acknowledged by the leader itself at the new
position), and a heartbeat goes to every peer with the new position as its context
(`hbCtx`, of the queue with the request). The request's entries are read-only (the queue
keeps the message).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- The request `m` (entries `ents`) arriving at the leader in state `s`: its record. -/
def arriveReq (s : NState) (m : raftpb.Message) (ents : List raftpb.Entry) : ReadReq :=
  ⟨s.logst.committed, m.From', ents⟩

/-- ... and the state with it queued (before the heartbeats). -/
def arriveState (id : w64) (s : NState) (m : raftpb.Message) (ents : List raftpb.Entry) :
    NState :=
  { s with rd := { s.rd with ro := readonlyArrive s.rd.ro id (arriveReq s m ents) } }

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev sendMsgReadIndexResponse.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry),
  s.role = .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysC c r id s ∗
      "#Hents" ∷ m.Entries' ↦*□ ents }}
    (App (App (Val #(functions sendMsgReadIndexResponse [])) (Val #r)) (Val #m))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysC c r id { sendMsgs (arriveState id s m ents) ms with prvals := pvs } ∗
      ⌜∀ m' ∈ ms, HeartbeatOk id (toPState s) m' ∧
         m'.ctx = hbCtx (readonlyAdd s.rd.ro (arriveReq s m ents))⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `sendMsgReadIndexResponse.spec` by `sendMsgReadIndexResponse.spec_simple`. -/
abbrev sendMsgReadIndexResponse.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry),
  s.role = .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "#Hents" ∷ m.Entries' ↦*□ ents }}
    (App (App (Val #(functions sendMsgReadIndexResponse [])) (Val #r)) (Val #m))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhys cfg r id { sendMsgs (arriveState id s m ents) ms with prvals := pvs } ∗
      ⌜∀ m' ∈ ms, HeartbeatOk id (toPState s) m' ∧
         m'.ctx = hbCtx (readonlyAdd s.rd.ro (arriveReq s m ents))⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

open Iris.ProofMode in
theorem sendMsgReadIndexResponse.spec_simple
    (H : sendMsgReadIndexResponse.spec (GF := GF) (hG := hG)) :
    sendMsgReadIndexResponse.specS (GF := GF) (hG := hG) := by
  intro cfg r id s m ents Hl
  iintro %Φ ⟨#Hpkg, Hphys, #Hents⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s m ents Hl $$ [$Hpkg $Hphys $Hents]
  inext
  iintro %ms %pvs ⟨Hphys, %H1, %H2⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  iframe Hphys
  ipureintro; exact ⟨H1, H2⟩

end spec

end EtcdGrove
end Perennial
