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

raft v3.7 (2026-10-15, stage R4): `req` is a `*pb.Message`, frozen (`msgOwn req □`: it is the
read-only queue's or the pending slice's, or `stepLeader`'s frozen `MsgReadIndex`), read through
its getters; the result is a fresh `*pb.Message`, owned (`msgOwn resp 1`): the empty
`&pb.Message{}` for a local request, else the response, whose `To` cell and `Entries` slice are
the request's (shared, read-only), so it holds the request's entries. (D6) The `ReadState`'s
context is the bytes of the request's first entry (`ReadStateM`; `r.readStates` holds the Go
structs with their `RequestCtx` slices read-only, `readStatesPts`).
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

/-- The response to a forwarded read-index request (stage R4: its scalars; the entries, the
request's, are the message state's, `MsgSt.ents`). -/
def readIndexRespMsg (req : MessageM) (idx : w64) : MessageM :=
  { (zero_val MessageM) with
      Type' := W32 16
      To' := req.From'
      Index' := idx }

/-- A local request's `ReadState`, appended. -/
def addReadState (s : NState) (idx : w64) (ctx : List w8) : NState :=
  { s with rd := { s.rd with states := s.rd.states ++ [ReadStateM.mk idx ctx] } }

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.responseToReadIndexReq.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (req : Loc) (m : MessageM) (idx : w64)
    (e : EntryM) (es : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hreq" ∷ msgOwn req DFrac.discard ⟨m, e :: es, sn, ctx, rs⟩ }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"responseToReadIndexReq"))
      (Val #req)) (Val #idx))
  {{ (resp : Loc), RET #resp;
      if m.From' = W64 0 ∨ m.From' = id then
        ownRaftPhysCV c c.voters r id (addReadState s idx e.Data') ∗
          msgOwn resp (DFrac.own 1) ⟨zero_val MessageM, [], none, [], []⟩
      else
        ownRaftPhysCV c c.voters r id s ∗
          msgOwn resp (DFrac.own 1) ⟨readIndexRespMsg m idx, e :: es, none, [], []⟩ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.responseToReadIndexReq.spec` by `raft.responseToReadIndexReq.spec_simple`. -/
abbrev raft.responseToReadIndexReq.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (req : Loc) (m : MessageM) (idx : w64)
    (e : EntryM) (es : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "#Hreq" ∷ msgOwn req DFrac.discard ⟨m, e :: es, sn, ctx, rs⟩ }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"responseToReadIndexReq"))
      (Val #req)) (Val #idx))
  {{ (resp : Loc), RET #resp;
      if m.From' = W64 0 ∨ m.From' = id then
        ownRaftPhys cfg r id (addReadState s idx e.Data') ∗
          msgOwn resp (DFrac.own 1) ⟨zero_val MessageM, [], none, [], []⟩
      else
        ownRaftPhys cfg r id s ∗
          msgOwn resp (DFrac.own 1) ⟨readIndexRespMsg m idx, e :: es, none, [], []⟩ }}

open Iris.ProofMode in
theorem raft.responseToReadIndexReq.spec_simple
    (H : raft.responseToReadIndexReq.spec (GF := GF) (hG := hG)) :
    raft.responseToReadIndexReq.specS (GF := GF) (hG := hG) := by
  intro cfg r id s req m idx e es sn ctx rs
  iintro %Φ ⟨#Hpkg, Hphys, #Hreq⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s req m idx e es sn ctx rs $$ [$Hpkg $Hphys $Hreq]
  inext
  iintro %resp Hpost
  iapply HΦ
  by_cases Hc : m.From' = W64 0 ∨ m.From' = id
  · simp only [Hc, ↓reduceIte]
    icases Hpost with ⟨Hphys, Hr⟩
    ihave Hphys := ownRaftPhysC_toS $$ Hphys
    iframe Hphys Hr
  · simp only [Hc, ↓reduceIte]
    icases Hpost with ⟨Hphys, Hr⟩
    ihave Hphys := ownRaftPhysC_toS $$ Hphys
    iframe Hphys Hr

end spec

end EtcdGrove
end Perennial
