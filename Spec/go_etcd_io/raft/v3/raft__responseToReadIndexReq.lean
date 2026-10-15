/- Lean-first (no Rocq counterpart; 2026-10-12, read-index).

## `raft.responseToReadIndexReq(req, readIndex)` (raft.go:2062)

    if req.From == None || req.From == r.id {
        r.readStates = append(r.readStates, ReadState{Index: readIndex,
            RequestCtx: req.Entries[0].Data})
        return pb.Message{}
    }
    return pb.Message{Type: pb.MsgReadIndexResp, To: req.From, Index: readIndex,
        Entries: req.Entries}

A local request (no sender, or the node's own) becomes a `ReadState`, its context the
request's first entry's data; a forwarded one becomes the response to send back. The
request has at least one entry (`req.Entries[0]` faults otherwise), read-only.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- The response to a forwarded read-index request. -/
def readIndexRespMsg (req : raftpb.Message) (idx : w64) : raftpb.Message :=
  { (zero_val raftpb.Message) with
      Type' := W32 16
      To' := req.From'
      Index' := idx
      Entries' := req.Entries' }

/-- A local request's `ReadState`, appended. -/
def addReadState (s : NState) (idx : w64) (ctx : GoSlice) : NState :=
  { s with rd := { s.rd with states := s.rd.states ++ [ReadState.mk idx ctx] } }

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.responseToReadIndexReq.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (req : raftpb.Message) (idx : w64)
    (e : raftpb.Entry) (es : List raftpb.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hents" ∷ req.Entries' ↦*□ (e :: es) }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"responseToReadIndexReq"))
      (Val #req)) (Val #idx))
  {{ (resp : raftpb.Message), RET #resp;
      if req.From' = W64 0 ∨ req.From' = id then
        ownRaftPhysCV c c.voters r id (addReadState s idx e.Data') ∗ ⌜resp.To' = W64 0⌝
      else
        ownRaftPhysCV c c.voters r id s ∗ ⌜resp = readIndexRespMsg req idx⌝ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.responseToReadIndexReq.spec` by `raft.responseToReadIndexReq.spec_simple`. -/
abbrev raft.responseToReadIndexReq.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (req : raftpb.Message) (idx : w64)
    (e : raftpb.Entry) (es : List raftpb.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "#Hents" ∷ req.Entries' ↦*□ (e :: es) }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"responseToReadIndexReq"))
      (Val #req)) (Val #idx))
  {{ (resp : raftpb.Message), RET #resp;
      if req.From' = W64 0 ∨ req.From' = id then
        ownRaftPhys cfg r id (addReadState s idx e.Data') ∗ ⌜resp.To' = W64 0⌝
      else
        ownRaftPhys cfg r id s ∗ ⌜resp = readIndexRespMsg req idx⌝ }}

open Iris.ProofMode in
theorem raft.responseToReadIndexReq.spec_simple
    (H : raft.responseToReadIndexReq.spec (GF := GF) (hG := hG)) :
    raft.responseToReadIndexReq.specS (GF := GF) (hG := hG) := by
  intro cfg r id s req idx e es
  iintro %Φ ⟨#Hpkg, Hphys, #Hents⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s req idx e es $$ [$Hpkg $Hphys $Hents]
  inext
  iintro %resp Hpost
  iapply HΦ
  by_cases Hc : req.From' = W64 0 ∨ req.From' = id
  · simp only [Hc, ↓reduceIte]
    icases Hpost with ⟨Hphys, %Hr⟩
    ihave Hphys := ownRaftPhysC_toS $$ Hphys
    iframe Hphys
    ipureintro; exact Hr
  · simp only [Hc, ↓reduceIte]
    icases Hpost with ⟨Hphys, %Hr⟩
    ihave Hphys := ownRaftPhysC_toS $$ Hphys
    iframe Hphys
    ipureintro; exact Hr

end spec

end EtcdGrove
end Perennial
