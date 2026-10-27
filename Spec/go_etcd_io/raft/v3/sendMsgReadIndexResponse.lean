/- Lean-first (no Rocq counterpart; 2026-10-12, read-index).

## `sendMsgReadIndexResponse(r, m)` (raft.go:2130)

    if _, isVoter := r.trk.Voters[0][r.id]; isVoter && r.trk.IsSingleton() {
        if resp := r.responseToReadIndexReq(m, r.raftLog.committed); resp.To != None {
            r.send(resp)
        }
        return
    }
    switch r.readOnly.option {
    case ReadOnlySafe:
        r.readOnly.addRequest(r.raftLog.committed, m)
        r.readOnly.recvAck(r.id, r.readOnly.heartbeatCtx())
        r.bcastHeartbeat()
    case ReadOnlyLeaseBased: ...
    }

Since 2026-10-14 the pinned raft is the fork revision with the single-voter fix
(`issues/raft-readindex-singleton-stale.md`): at a configuration whose only voter is the
leader itself (`CfgSingle`), the request is answered at once at the commit index
(`readRespond`: a local one becomes a `ReadState`, a forwarded one a `MsgReadIndexResp`); the
caller has checked `committedEntryInCurrentTerm`. The request has entries (`req.Entries[0]`).

Otherwise the option is `ReadOnlySafe` (`ownReadOnly`). The request is queued, read at the commit
index (`readonlyArrive`: queued, then acknowledged by the leader itself at the new
position), and a heartbeat goes to every peer with the new position as its context
(`hbCtx`, of the queue with the request). The request's entries are read-only (the queue
keeps the message).

raft v3.7 (2026-10-15, stage R4): `m` is a `*pb.Message` (`ml`), frozen (`msgOwn ml □`): the queue
keeps the pointer (`ownReadreq`), `responseToReadIndexReq` shares its `Entries`; the record's
scalars `m` and entries `ents` as before.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__responseToReadIndexReq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [GooseExts]

/-- The request `m` (entries `ents`) arriving at the leader in state `s`: its record. -/
def arriveReq (s : NState) (m : MessageM) (ents : List EntryM) : ReadReq :=
  ⟨s.logst.committed, m.From', ents⟩

/-- ... and the state with it queued (before the heartbeats). -/
def arriveState (id : w64) (s : NState) (m : MessageM) (ents : List EntryM) :
    NState :=
  { s with rd := { s.rd with ro := readonlyArrive s.rd.ro id (arriveReq s m ents) } }

/-- A confirmed read-index request answered (2026-10-12, `responseToReadIndexReq` and the
`send`): a local one becomes a `ReadState` (its context the first entry's data), a
forwarded one a `MsgReadIndexResp` to its sender. (Moved here from `Spec/stepLeader.lean` on
2026-10-14.) -/
def readRespond (id : w64) (s : NState) (q : ReadReq) : NState :=
  if q.src = W64 0 ∨ q.src = id then
    match q.ents with
    | e :: _ => addReadState s q.index e.Data'
    | [] => s
  else sendMsgs s [Msg.mk .readIndexResp id q.src s.term false q.index (W64 0) (W64 0)
                     (W64 0) q.ents]

def readRespondAll (id : w64) (s : NState) (qs : List ReadReq) : NState :=
  qs.foldl (readRespond id) s

/-- `readRespond` changes only the outbox and the read state (2026-10-13). -/
theorem readRespond_eq (id : w64) (s : NState) (q : ReadReq) :
    ∃ o r, readRespond id s q = { s with outbox := o, rd := r } := by
  unfold readRespond
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨s.outbox, s.rd, by cases s; rfl⟩
  · exact ⟨_, _, rfl⟩

theorem readRespondAll_eq (id : w64) (s : NState) (qs : List ReadReq) :
    ∃ o r, readRespondAll id s qs = { s with outbox := o, rd := r } := by
  unfold readRespondAll
  induction qs generalizing s with
  | nil => exact ⟨s.outbox, s.rd, by cases s; rfl⟩
  | cons q qs ih =>
    rw [List.foldl_cons]
    obtain ⟨o1, r1, h1⟩ := readRespond_eq id s q
    rw [h1]
    exact ih { s with outbox := o1, rd := r1 }

theorem readRespondAll_fields (id : w64) (s : NState) (qs : List ReadReq) :
    (readRespondAll id s qs).logst = s.logst ∧ (readRespondAll id s qs).role = s.role ∧
    (readRespondAll id s qs).term = s.term := by
  obtain ⟨o, r, h⟩ := readRespondAll_eq id s qs
  rw [h]; exact ⟨rfl, rfl, rfl⟩

/-- (D19p) Answering keeps the progress map. -/
theorem readRespondAll_progress (id : w64) (s : NState) (qs : List ReadReq) :
    (readRespondAll id s qs).progress = s.progress := by
  obtain ⟨o, r, h⟩ := readRespondAll_eq id s qs
  rw [h]

/-- (D21 M3) Answering keeps the ghost bounds and the mode. -/
theorem readRespondAll_gh (id : w64) (s : NState) (qs : List ReadReq) :
    (readRespondAll id s qs).gh = s.gh := by
  obtain ⟨o, r, h⟩ := readRespondAll_eq id s qs
  rw [h]

/-- Answering does not read the `Progress` values. -/
theorem readRespondAll_prvals (id : w64) (t : NState) (pv : GMap w64 Progress)
    (qs : List ReadReq) :
    readRespondAll id { t with prvals := pv } qs = { readRespondAll id t qs with prvals := pv } := by
  induction qs generalizing t with
  | nil => rfl
  | cons q qs ih =>
    have e : readRespond id { t with prvals := pv } q = { readRespond id t q with prvals := pv } := by
      unfold readRespond
      split
      · split <;> rfl
      · rfl
    show readRespondAll id (readRespond id { t with prvals := pv } q) qs =
      { readRespondAll id (readRespond id t q) qs with prvals := pv }
    rw [e, ih]

theorem readRespondAll_take_succ (id : w64) (s : NState) (qs : List ReadReq) (n : Nat)
    (q : ReadReq) (H : qs[n]? = some q) :
    readRespondAll id s (qs.take (n + 1)) = readRespond id (readRespondAll id s (qs.take n)) q := by
  unfold readRespondAll
  rw [List.take_add_one, H]
  simp [List.foldl_append]

/-- What `sendMsgReadIndexResponse` does with the request `m` (entries `ents`) at the leader in
state `s` at the configuration `c` (2026-10-14): at a configuration whose only voter is the
leader itself, answered at once at the commit index; otherwise queued, and heartbeats with the
new position broadcast. -/
def SendRIResult (c : CfgM) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (s' : NState) : Prop :=
  (CfgSingle c id ∧ s' = readRespond id s (arriveReq s m ents)) ∨
  (¬ CfgSingle c id ∧ ∃ (ms : List Msg) (pvs : GMap w64 Progress),
     s' = { sendMsgs (arriveState id s m ents) ms with prvals := pvs } ∧
     (∀ m' ∈ ms, HeartbeatOk id (toPState s) m' ∧
        m'.ctx = hbCtx (readonlyAdd s.rd.ro (arriveReq s m ents))) ∧
     prvalsMatch pvs = prvalsMatch s.prvals)

end results

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev sendMsgReadIndexResponse.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc),
  s.role = .leader →
  ents ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hm" ∷ msgOwn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
    (App (App (Val #(functions sendMsgReadIndexResponse [])) (Val #r)) (Val #ml))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗ ⌜SendRIResult c id s m ents s'⌝ }}

end spec

end EtcdGrove
end Perennial
