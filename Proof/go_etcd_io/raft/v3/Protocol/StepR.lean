/-
The protocol's step relation with what reconfiguration reads (2026-10-14, reconfiguration
stage B3), Lean-first: pure, no ghost state. The paper proof it serves is
`notes/reconfiguration-safety.md` (sections 2-4).

`StepC c id` (`StepC.lean`) is a node's step at a configuration `c` that is a parameter: nothing
in its state says which conf-change entries `c` reflects, and nothing in it moves `c`. `StepR`
is a node's step on `RState`, the protocol state `PState` together with what Go's guards read
and what makes a configuration move:

* `applied` (`raftLog.applied`), `pci` (`r.pendingConfIndex`), `snap` (a snapshot restored and
  not yet applied: `hasNextOrInProgressSnapshot`, which makes the node unpromotable);
* the configuration `cfg` (a `CCState`: `confchange`'s `Config` and learner flags) and its
  *configuration index* `cidx`: the configuration is that of the full log's first `cidx`
  entries (`RInv.cfg`, `StepRInv.lean`);
* `fp`, ghost: the full log's prefix below the compaction boundary `p.base` (as the ghost
  state's `FullOk` logs), so that `full r = fp ++ p.log` is the node's log from `base0`, the
  log a decoder (`CCDec`, `CfgOverlap.lean`) reads a conf entry's prefix from.

The rules are `StepC`'s at `cfg.cfg`, with Go's guards and side effects on the new fields, and
four new rules:

* `campaign` has `hup`'s guard: `promotable` (`id` a voter, no pending snapshot) and no conf
  entry in `(applied, commit]` (`hasUnappliedConfChanges`), and `reset` clears `pci`. (Go
  checks the guard at `hup`; the campaign after a pre-vote win, `stepCandidate`, checks
  nothing, but the guard still holds there: notes/reconfiguration-safety.md 4.1, review 10.)
* `win` sets `pci` to the last index before the leader's empty entry (`becomeLeader`).
* `propose` runs `stepLeader`'s conf-change loop exactly (`propConf` with `applied`, `pci` and
  `alreadyJoint`), where `StepC.propose` allowed any `PropRepl` replacement; `propDrop` is the
  loop's effect on `pci` when `appendEntry` then refuses the batch (receiving nothing, as the
  code's dropped proposal takes no protocol step).
* `sendApps`/`win` send `MsgApp`s carrying the leader's commit index (`AppCommitEq`: Go's
  `sendAppend` sets `Commit: r.raftLog.committed`); `StepC`'s `AppOk` allows any smaller one,
  under which I1 is false (`notes/reconfiguration-safety.md`'s I1 on `MsgApp` slices; see
  `StepRInv.lean`, "I1 needs the commit index").
* `higherTerm`, `stepDown` clear `pci` (`reset`); the other rules that make a follower leave it
  (a non-leader's is `0` in Go, and nothing reads it).
* `snapRestore` takes the snapshot's configuration (`restore`'s `ConfState`) as the node's, at
  the snapshot's index, with the snapshot pending; the node's full prefix becomes `fp'`, ghost.
* new: `advance` (`applied` moves up to at most `commit`, past no conf entry the configuration
  has not taken: A1, `ApplyConfChange` before `Advance`), `applySnap` (`appliedSnap`: the
  pending snapshot applied), `applyConf` (the configuration takes the next conf entry, in
  order, once per entry, decoded by `dec` from the entry and its prefix: the review's A1 gap),
  `stepDown` (a leader outside its configuration's voters becomes a follower at its term:
  `switchToConfig` with `StepDownOnRemoval`; without it the leader stays, which the model
  allows by not taking the rule).

`Adm l cs`: the configurations a node may take on after the full-log prefix `l` (by
`applyConf`, or as a snapshot's by `snapRestore`). The dynamic model takes the fold of the
prefix (`AdmFold`: A3, a snapshot's `ConfState` is its prefix's configuration; for `applyConf`
it is implied by the decoder); the static one (`StaticAdm V`) the voters `V` unchanged. (Until
D19p, 2026-10-18, `StepR` projected to `StepC (CfgM.simple V ∅)` there, `stepR_static`, and so
refined the ghost state, `ownRaftGhost_stepR`: `StepC`'s broadcasts now send a snapshot only to a
voter or learner of their configuration, which a learner-free `StepC` cannot express; unused,
both were removed.) `StepR.mono`: a derivation under `Adm` is one under any weaker `Adm'`.

Nothing in the code produces a `StepR` witness yet (notes/STATUS.md, "Reconfiguration, stage
B3").
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.CfgOverlap

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open GMap go_etcd_io.raft.v3

section state
variable [FfiSyntax]

/-- A node's protocol state with what reconfiguration reads (see the file header). -/
structure RState where
  /-- the protocol state of `StepC` -/
  p : PState
  /-- `raftLog.applied` -/
  applied : w64
  /-- `r.pendingConfIndex` -/
  pci : w64
  /-- a snapshot restored and not yet applied (`hasNextOrInProgressSnapshot`) -/
  snap : Bool
  /-- the configuration index: `cfg` is the configuration of the full log's first `cidx`
  entries -/
  cidx : Nat
  /-- the configuration in use, with the learner flags (`confchange`'s state) -/
  cfg : CCState
  /-- ghost: the full log's prefix below `p.base` -/
  fp : List EntryM

/-- The node's full log, from `base0`: the entry at log index `i` is at position `i - 1`. -/
def RState.full (r : RState) : List EntryM := r.fp ++ r.p.log

/-- No conf-change entry at the positions `[lo, hi)` of `l` (log indices `(lo, hi]`). -/
def NoConfIn (l : List EntryM) (lo hi : Nat) : Prop :=
  ∀ (k : Nat) (e : EntryM), lo ≤ k → k < hi → l[k]? = some e → ¬ IsConfEnt e

/-- `stepLeader`'s conf-change loop at `r`: the batch and the new `pendingConfIndex`. -/
def propBatch (r : RState) (ents : List EntryM) (cs : List (Option CCMsg)) :
    List EntryM × w64 :=
  propConf r.applied (plastIndex r.p) r.pci ents cs (CfgM.joint r.cfg.cfg)

/-- (2026-10-20, witness support) `maybeStartNewSubterm` at a leader: the next subterm, its
replication set excluding `x` (`0` for the witness), of the configuration of the prefix `P`
(ghost, `PState.scp`), with an empty entry of it and its self-acknowledgement (`StepC.newSub`'s
effect). -/
abbrev pnewSub (id : w64) (p : PState) (x : w64) (P : List EntryM) : PState :=
  psendMsgs (pappend { p with sub := p.sub + W64 1, rsx := x, scp := P }
      [stampS p.term (p.sub + W64 1) (plastIndex p) 0 (zero_val EntryM)])
    [pselfAck id (pappend { p with sub := p.sub + W64 1, rsx := x, scp := P }
      [stampS p.term (p.sub + W64 1) (plastIndex p) 0 (zero_val EntryM)])]

/-- The dynamic model's configurations: the fold of the prefix from `c0` (A3). -/
def AdmFold (dec : CCDec) (c0 : CCState) (l : List EntryM) (cs : CCState) : Prop :=
  cfgFold dec c0 l = some cs

/-- The static model's configurations: voters `V`, not joint (learners free). -/
def StaticAdm (V : GSet w64) (_ : List EntryM) (cs : CCState) : Prop :=
  cs.cfg.incoming = V ∧ cs.cfg.outgoing = ∅

end state

section model
variable [FfiSyntax]

variable (Adm : List EntryM → CCState → Prop) (dec : CCDec) (id : w64)

/- (2026-10-18, D19b stage 5) As `StepC`'s: the rules that create entries (`win`, `propose`)
take their last index at most `B`. -/
variable (B : Int)

/-- A node's step with reconfiguration (see the file header). The rules shared with `StepC`
are its rules at `r.cfg.cfg` on `r.p`; their documentation is `Step`'s. -/
inductive StepR : RState → List Msg → RState → Prop where
  | refl (r : RState) : StepR r [] r
  | trans (r₀ : RState) (m₁ : List Msg) (r₁ : RState) (m₂ : List Msg) (r₂ : RState) :
      StepR r₀ m₁ r₁ → StepR r₁ m₂ r₂ → StepR r₀ (m₁ ++ m₂) r₂
  | higherTerm (m : Msg) (r : RState) :
      uint.Z r.p.term < uint.Z m.term →
      m.dst = id →
      (fromLeader m.ty = true → m.src ≠ id) →
      StepR r [m] { r with
        p := pbecomeFollower r.p m.term (if fromLeader m.ty then m.src else W64 0)
        pci := W64 0 }
  | campaign (r : RState) (peers : List w64) (cl : List w8) :
      r.p.role ≠ .leader →
      id ∈ r.cfg.cfg.voters →
      r.snap = false →
      NoConfIn r.full (uint.nat r.applied) (uint.nat r.p.commit) →
      uint.Z r.p.term + 1 < 2 ^ 64 →
      peers ≡ₚ elements (r.cfg.cfg.voters \ {[id]}) →
      StepR r [] { r with
        p := psendMsgs (pbecomeCandidate id r.p)
          ([Msg.plain .voteResp id id (pbecomeCandidate id r.p).term false] ++
           peers.map (fun dst => pvoteReq id dst (pbecomeCandidate id r.p).term
                                   (plogLast r.p.base r.p.log) cl))
        pci := W64 0 }
  | grantVote (m : Msg) (r : RState) :
      m.ty = .vote →
      m.dst = id →
      m.src ≠ W64 0 →
      m.term = r.p.term →
      PCanVote r.p m.src →
      plogUpToDate r.p.base r.p.log (entryID.mk m.logterm m.index) = true →
      StepR r [m] { r with
        p := psendMsgs { r.p with vote := m.src } [Msg.plain .voteResp id m.src r.p.term false] }
  | rejectVote (m : Msg) (r : RState) :
      m.ty = .vote →
      m.dst = id →
      StepR r [m] { r with p := psendMsgs r.p [Msg.plain .voteResp id m.src r.p.term true] }
  | recordVote (m : Msg) (r : RState) :
      m.ty = .voteResp →
      m.dst = id →
      m.term = r.p.term →
      r.p.role = .candidate →
      StepR r [m] { r with p := { r.p with votes := recordVote r.p.votes m.src (!m.reject) } }
  | win (r : RState) (mt : GMap w64 w64) (ms : List Msg) :
      r.p.role = .candidate →
      JQuorum r.cfg.cfg (granted r.p.votes) →
      plogLastIndexZ r.p.base r.p.log + 1 ≤ B →
      LeaderMatchOk id r.p mt →
      (∀ m ∈ ms, ReplOk id (pwinState id r.p mt) m) →
      (∀ m ∈ ms, AppCommitEq (pwinState id r.p mt) m) →
      StepR r [] { r with
        p := psendMsgs (pwinState id r.p mt) ([pselfAck id (pwinState id r.p mt)] ++ ms)
        pci := plastIndex r.p }
  | lose (r : RState) :
      r.p.role = .candidate →
      JLost r.cfg.cfg r.p.votes →
      StepR r [] { r with p := pbecomeFollower r.p r.p.term (W64 0) }
  | drain (r : RState) (o' : List Msg) :
      o'.Subperm r.p.outbox →
      StepR r [] { r with p := { r.p with outbox := o' } }
  | appAccept (m : Msg) (r : RState) (lastnewi : w64) (es' : List EntryM) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = r.p.term →
      r.p.role ≠ .leader →
      uint.Z r.p.commit ≤ uint.Z m.index →
      plogMaybeAppend r.p.base r.p.log (entryID.mk m.logterm m.index) m.entries
        = some (lastnewi, es') →
      (plogFindConflict r.p.base r.p.log m.entries = W64 0 ∨
        uint.Z r.p.commit < uint.Z (plogFindConflict r.p.base r.p.log m.entries)) →
      StepR r [m] { r with
        p := psendMsgs
          { padoptLeader r.p m.src with
              log := es',
              commit := plogCommitTo r.p.commit
                          (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) }
          [Msg.mk .appResp id m.src r.p.term false lastnewi (W64 0) (W64 0) (W64 0) []] }
  | appStale (m : Msg) (r : RState) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = r.p.term →
      r.p.role ≠ .leader →
      uint.Z m.index < uint.Z r.p.commit →
      StepR r [m] { r with
        p := psendMsgs (padoptLeader r.p m.src)
          [Msg.mk .appResp id m.src r.p.term false r.p.commit (W64 0) (W64 0) (W64 0) []] }
  | appReject (m : Msg) (r : RState) (hint hintterm : w64) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = r.p.term →
      r.p.role ≠ .leader →
      uint.Z r.p.commit ≤ uint.Z m.index →
      ¬ PlogMatches r.p.base r.p.log (entryID.mk m.logterm m.index) →
      RejHintOk r.p.base r.p.log m.index m.logterm hint →
      StepR r [m] { r with
        p := psendMsgs (padoptLeader r.p m.src)
          [Msg.mk .appResp id m.src r.p.term true m.index hintterm (W64 0) hint []] }
  | heartbeat (m : Msg) (r : RState) :
      m.ty = .heartbeat →
      m.dst = id →
      m.src ≠ id →
      m.term = r.p.term →
      r.p.role ≠ .leader →
      uint.Z m.commit ≤ plogLastIndexZ r.p.base r.p.log →
      StepR r [m] { r with
        p := psendMsgs
          { padoptLeader r.p m.src with commit := plogCommitTo r.p.commit m.commit }
          [{ Msg.plain .heartbeatResp id m.src r.p.term false with ctx := m.ctx }] }
  | beat (r : RState) (ms : List Msg) :
      r.p.role = .leader →
      (∀ m ∈ ms, HeartbeatOk id r.p m) →
      (∀ m ∈ ms, HbCtxOk r.p.rd.ro m.ctx) →
      StepR r [] { r with p := psendMsgs r.p ms }
  | appResp (m : Msg) (r : RState) (x : w64) :
      m.ty = .appResp →
      m.dst = id →
      m.term = r.p.term →
      r.p.role = .leader →
      m.reject = false →
      r.p.matched !! m.src = some x →
      StepR r [m] { r with p := { r.p with matched :=
            (<[m.src := (if uint.Z x < uint.Z m.index then m.index else x)]> r.p.matched) } }
  | commit (r : RState) (n : w64) :
      r.p.role = .leader →
      uint.Z r.p.commit < uint.Z n →
      uint.Z n ≤ plogLastIndexZ r.p.base r.p.log →
      plogTermAt r.p.base r.p.log n = some r.p.term →
      JQuorum r.cfg.cfg (ackedBy r.p n) →
      StepR r [] { r with p := { r.p with commit := n } }
  | sendApps (r : RState) (ms : List Msg) :
      r.p.role = .leader →
      (∀ m ∈ ms, ReplOk id r.p m) →
      (∀ m ∈ ms, AppCommitEq r.p m) →
      StepR r [] { r with p := psendMsgs r.p ms }
  | propose (m : Msg) (r : RState) (cs : List (Option CCMsg)) :
      m.ty = .propose →
      r.p.role = .leader →
      CCTypesOk m.entries cs →
      plogLastIndexZ r.p.base r.p.log + (m.entries.length : Int) ≤ B →
      StepR r [m] { r with
        p := psendMsgs
          (pappend r.p ((propBatch r m.entries cs).1.mapIdx
            (stampS r.p.term r.p.sub (plastIndex r.p))))
          [pselfAck id (pappend r.p
            ((propBatch r m.entries cs).1.mapIdx (stampS r.p.term r.p.sub (plastIndex r.p))))]
        pci := (propBatch r m.entries cs).2 }
  | propDrop (m : Msg) (r : RState) (cs : List (Option CCMsg)) :
      m.ty = .propose →
      r.p.role = .leader →
      CCTypesOk m.entries cs →
      plogLastIndexZ r.p.base r.p.log + (m.entries.length : Int) < 2 ^ 64 →
      StepR r [] { r with pci := (propBatch r m.entries cs).2 }
  | propForward (m : Msg) (r : RState) :
      m.ty = .propose →
      r.p.role = .follower →
      r.p.lead ≠ W64 0 →
      StepR r [m] { r with
        p := psendMsgs r.p
          [Msg.mkV .propose id r.p.lead (W64 0) m.reject m.index m.logterm m.commit
             m.rejecthint m.entries [] m.ctx] }
  | snapRestore (m : Msg) (r : RState) (fp' : List EntryM) (cs' : CCState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = r.p.term →
      r.p.role ≠ .leader →
      uint.Z r.p.commit < uint.Z m.index →
      ¬ PlogMatches r.p.base r.p.log (entryID.mk m.logterm m.index) →
      FullOk (entryID.mk m.logterm m.index) fp' →
      id ∈ cs'.cfg.ids →
      Adm fp' cs' →
      StepR r [m] { r with
        p := psendMsgs
          { padoptLeader r.p m.src with
              base := entryID.mk m.logterm m.index, log := [], commit := m.index }
          [Msg.mk .appResp id m.src r.p.term false m.index (W64 0) (W64 0) (W64 0) []]
        snap := true
        cidx := uint.nat m.index
        cfg := cs'
        fp := fp' }
  | snapFastfwd (m : Msg) (r : RState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = r.p.term →
      r.p.role ≠ .leader →
      uint.Z r.p.commit < uint.Z m.index →
      PlogMatches r.p.base r.p.log (entryID.mk m.logterm m.index) →
      StepR r [m] { r with
        p := psendMsgs { padoptLeader r.p m.src with commit := m.index }
          [Msg.mk .appResp id m.src r.p.term false m.index (W64 0) (W64 0) (W64 0) []] }
  | snapStale (m : Msg) (r : RState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = r.p.term →
      r.p.role ≠ .leader →
      uint.Z m.index ≤ uint.Z r.p.commit →
      StepR r [m] { r with
        p := psendMsgs (padoptLeader r.p m.src)
          [Msg.mk .appResp id m.src r.p.term false r.p.commit (W64 0) (W64 0) (W64 0) []] }
  | takeReads (r : RState) :
      StepR r [] { r with p := { r.p with rd := { r.p.rd with states := [] } } }
  | readFwd (m : Msg) (r : RState) :
      m.ty = .readIndex → r.p.role ≠ .leader → r.p.lead ≠ W64 0 →
      StepR r [m] { r with p := psendMsgs r.p [{ m with
        src := if m.src = W64 0 then id else m.src
        dst := r.p.lead
        term := W64 0 }] }
  | readPend (m : Msg) (r : RState) (pm : MessageM) :
      m.ty = .readIndex → r.p.role = .leader → m.src = pm.From' →
      StepR r [m] { r with p :=
        { r.p with rd := { r.p.rd with pend := r.p.rd.pend ++ [(pm, m.entries)] } } }
  | readArrive (m : Msg) (r : RState) :
      m.ty = .readIndex → r.p.role = .leader →
      plogTermAt r.p.base r.p.log r.p.commit = some r.p.term →
      StepR r [m] { r with p := { r.p with rd := { r.p.rd with
                     ro := readonlyArrive r.p.rd.ro id ⟨r.p.commit, m.src, m.entries⟩ } } }
  | readRelease (r : RState) :
      r.p.role = .leader → plogTermAt r.p.base r.p.log r.p.commit = some r.p.term →
      StepR r [] { r with p := { r.p with rd := { r.p.rd with
        pend := []
        ro := readonlyRelease r.p.rd.ro id r.p.commit r.p.rd.pend } } }
  /-- `sendMsgReadIndexResponse` at a single voter that is the leader itself (2026-10-14, the
  fix of `issues/raft-readindex-singleton-stale.md`): answered at once at the commit index. -/
  | readSingle (m : Msg) (r : RState) :
      m.ty = .readIndex → r.p.role = .leader →
      plogTermAt r.p.base r.p.log r.p.commit = some r.p.term → CfgSingle r.cfg.cfg id →
      StepR r [m] { r with p := preadRespondAll id r.p [⟨r.p.commit, m.src, m.entries⟩] }
  /-- `releasePendingReadIndexMessages` at a single voter that is the leader itself. -/
  | readReleaseSingle (r : RState) :
      r.p.role = .leader → plogTermAt r.p.base r.p.log r.p.commit = some r.p.term →
      CfgSingle r.cfg.cfg id →
      StepR r [] { r with p := (preadRespondAll id ({ r.p with rd := { r.p.rd with pend := [] } })
        (r.p.rd.pend.map (fun q => ⟨r.p.commit, q.1.From', q.2⟩))) }
  | readAck (m : Msg) (r : RState) (N : w64) :
      m.ty = .heartbeatResp → m.dst = id → m.term = r.p.term → r.p.role = .leader →
      m.ctx ≠ [] →
      JQuorumAcked r.cfg.cfg
        (fun v => ((readonlyRecvAck r.p.rd.ro m.src m.ctx).acks !! v).getD (W64 0)) N →
      StepR r [m] { r with p := (preadRespondAll id
        ({ r.p with rd := { r.p.rd with
             ro := (readonlyAdvance (readonlyRecvAck r.p.rd.ro m.src m.ctx) N).1 } })
        (readonlyAdvance (readonlyRecvAck r.p.rd.ro m.src m.ctx) N).2) }
  | readState (m : Msg) (r : RState) (e : EntryM) :
      m.ty = .readIndexResp → m.entries = [e] →
      StepR r [m] { r with p :=
        { r.p with rd := { r.p.rd with states := r.p.rd.states ++ [⟨m.index, e.Data'⟩] } } }
  | sendFree (r : RState) (m : Msg) :
      (m.ty = .preVote ∨ m.ty = .preVoteResp) →
      m.src = id →
      StepR r [] { r with p := psendMsgs r.p [m] }
  | abandon (r : RState) :
      r.p.role ≠ .leader →
      StepR r [] { r with p := pbecomeFollower r.p r.p.term (W64 0) }
  | zeroAck (r : RState) (dst : w64) :
      StepR r [] { r with p := psendMsgs r.p [Msg.mk .appResp id dst r.p.term false
                                (W64 0) (W64 0) (W64 0) (W64 0) []] }
  | reMatch (r : RState) (mt : GMap w64 w64) :
      r.p.role = .leader →
      (∀ v i, mt !! v = some i → uint.Z i = 0 ∨ r.p.matched !! v = some i) →
      StepR r [] { r with p := { r.p with matched := mt } }
  /-- `Advance`'s `appliedTo`: `applied` moves up to `a ≤ commit`, the configuration having
  taken every conf entry up to `a` (A1); the configuration index moves along when it was
  below. -/
  | advance (r : RState) (a : w64) :
      r.snap = false →
      uint.Z r.applied ≤ uint.Z a →
      uint.Z a ≤ uint.Z r.p.commit →
      NoConfIn r.full r.cidx (uint.nat a) →
      StepR r [] { r with applied := a, cidx := max r.cidx (uint.nat a) }
  /-- `appliedSnap`: the pending snapshot applied. -/
  | applySnap (r : RState) :
      r.snap = true →
      StepR r [] { r with applied := r.p.base.index', snap := false }
  /-- `ApplyConfChange` of the next conf entry (at position `k`, log index `k + 1`), committed,
  in order: the configuration takes its change, decoded from the entry and its prefix. -/
  | applyConf (r : RState) (k : Nat) (e : EntryM) (op : CCOp) (cs' : CCState) :
      r.snap = false →
      r.cidx ≤ k →
      k < uint.nat r.p.commit →
      r.full[k]? = some e →
      IsConfEnt e →
      NoConfIn r.full r.cidx k →
      dec (r.full.take k) e = some op →
      ccStepB op r.cfg = some cs' →
      Adm (r.full.take (k + 1)) cs' →
      -- (2026-10-20, witness support) a leader with a witness starts a new subterm with the
      -- change (`applyConfWit`)
      (r.p.role = .leader → r.cfg.cfg.wit = W64 0) →
      StepR r [] { r with cidx := k + 1, cfg := cs' }
  /-- (2026-10-20, witness support) `ApplyConfChange` at a leader, then `switchToConfig`'s new
  subterm (`maybeStartNewSubterm`), at the new configuration. -/
  | applyConfWit (r : RState) (k : Nat) (e : EntryM) (op : CCOp) (cs' : CCState) (x : w64) :
      r.snap = false →
      r.cidx ≤ k →
      k < uint.nat r.p.commit →
      r.full[k]? = some e →
      IsConfEnt e →
      NoConfIn r.full r.cidx k →
      dec (r.full.take k) e = some op →
      ccStepB op r.cfg = some cs' →
      Adm (r.full.take (k + 1)) cs' →
      r.p.role = .leader →
      (x = W64 0 ∨ (x ∈ cs'.cfg.incoming ∧ x ≠ cs'.cfg.wit)) →
      uint.Z r.p.sub + 1 < 2 ^ 64 →
      plogLastIndexZ r.p.base r.p.log + 1 ≤ B →
      StepR r [] { r with cidx := k + 1, cfg := cs', p := pnewSub id r.p x (r.full.take (k + 1)) }
  /-- (2026-10-20, witness support) `StepC.newSub` at the configuration. -/
  | newSub (r : RState) (x : w64) :
      r.p.role = .leader →
      r.cfg.cfg.wit ≠ W64 0 →
      (x = W64 0 ∨ (x ∈ r.cfg.cfg.incoming ∧ x ≠ r.cfg.cfg.wit)) →
      uint.Z r.p.sub + 1 < 2 ^ 64 →
      plogLastIndexZ r.p.base r.p.log + 1 ≤ B →
      StepR r [] { r with p := pnewSub id r.p x (r.full.take r.cidx) }
  /-- (2026-10-20) `StepC.sendWApp` at the configuration, whose witness is an incoming voter. -/
  | sendWApp (r : RState) (i : w64) (e : EntryM) (vs : List w64) :
      r.p.role = .leader →
      r.cfg.cfg.wit ≠ W64 0 →
      r.cfg.cfg.wit ∈ r.cfg.cfg.incoming →
      exclOf r.cfg.cfg r.p ≠ r.cfg.cfg.wit →
      exclOf r.cfg.cfg r.p ∈ r.cfg.cfg.incoming →
      plogEntryAt r.p.base r.p.log i = some e →
      e.Term' = r.p.term →
      e.Subterm' = r.p.sub →
      size r.cfg.cfg.incoming / 2 ≤ size (ackedBy r.p i ∩ rsVoters r.cfg.cfg r.p) →
      vs ≡ₚ elements (rsVoters r.cfg.cfg r.p) →
      StepR r [] { r with p := (psendMsgs r.p
        [Msg.mkV .wapp id r.cfg.cfg.wit r.p.term false i r.p.term r.p.sub (W64 0) [] vs []]) }
  /-- (2026-10-20) `StepC.askWitness` at the configuration. -/
  | askWitness (r : RState) (vs : List w64) :
      r.p.role = .candidate →
      r.cfg.cfg.wit ≠ W64 0 →
      size r.cfg.cfg.incoming / 2 ≤ size (granted r.p.votes ∩ r.cfg.cfg.incoming) →
      (r.cfg.cfg.outgoing ≠ ∅ →
        size r.cfg.cfg.outgoing / 2 ≤ size (granted r.p.votes ∩ r.cfg.cfg.outgoing)) →
      vs ≡ₚ elements (domSet r.p.votes) →
      StepR r [] { r with p := (psendMsgs r.p
        [Msg.mkV .wvote id r.cfg.cfg.wit r.p.term false (plogLast r.p.base r.p.log).index'
          (plogLast r.p.base r.p.log).term' (plogLastSub r.p.log) (W64 0) [] vs []]) }
  /-- (2026-10-20) `StepC.sendWPre`. -/
  | sendWPre (r : RState) (m : Msg) :
      r.cfg.cfg.wit ≠ W64 0 →
      m.ty = .wprevote →
      m.src = id →
      StepR r [] { r with p := psendMsgs r.p [m] }
  /-- A leader steps down at its term: `switchToConfig` with `StepDownOnRemoval` (a leader outside
  the voters), or (2026-10-17, `CheckQuorum` on; until then the rule required the leader outside
  its configuration's voters) `stepLeader`'s `MsgCheckQuorum` arm when the voters it heard from
  are no quorum. -/
  | stepDown (r : RState) :
      r.p.role = .leader →
      StepR r [] { r with p := pbecomeFollower r.p r.p.term (W64 0), pci := W64 0 }

end model

/-! ### Monotonicity in the admissible configurations -/

section mono
variable [FfiSyntax]

theorem StepR.mono {Adm Adm' : List EntryM → CCState → Prop} {dec : CCDec} {id : w64} {B : Int}
    (hA : ∀ l cs, Adm l cs → Adm' l cs) {r : RState} {ms : List Msg} {r' : RState}
    (h : StepR Adm dec id B r ms r') : StepR Adm' dec id B r ms r' := by
  induction h with
  | refl r => exact .refl r
  | trans _ _ _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ _ _ ih1 ih2
  | snapRestore m r fp' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .snapRestore m r fp' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 (hA _ _ h10)
  | applyConf r k e op cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .applyConf r k e op cs' h1 h2 h3 h4 h5 h6 h7 h8 (hA _ _ h9) h10
  | applyConfWit r k e op cs' x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
    exact .applyConfWit r k e op cs' x h1 h2 h3 h4 h5 h6 h7 h8 (hA _ _ h9) h10 h11 h12 h13
  | newSub r x h1 h2 h3 h4 h5 => exact .newSub r x h1 h2 h3 h4 h5
  | sendWApp r i e vs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .sendWApp r i e vs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | askWitness r vs h1 h2 h3 h4 h5 => exact .askWitness r vs h1 h2 h3 h4 h5
  | sendWPre r m h1 h2 h3 => exact .sendWPre r m h1 h2 h3
  | _ =>
    first
    | (apply StepR.higherTerm <;> assumption)
    | (apply StepR.campaign <;> assumption)
    | (apply StepR.grantVote <;> assumption)
    | (apply StepR.rejectVote <;> assumption)
    | (apply StepR.recordVote <;> assumption)
    | (apply StepR.win <;> assumption)
    | (apply StepR.lose <;> assumption)
    | (apply StepR.drain <;> assumption)
    | (apply StepR.appAccept <;> assumption)
    | (apply StepR.appStale <;> assumption)
    | (apply StepR.appReject <;> assumption)
    | (apply StepR.heartbeat <;> assumption)
    | (apply StepR.beat <;> assumption)
    | (apply StepR.appResp <;> assumption)
    | (apply StepR.commit <;> assumption)
    | (apply StepR.sendApps <;> assumption)
    | (apply StepR.propose <;> assumption)
    | (apply StepR.propDrop <;> assumption)
    | (apply StepR.propForward <;> assumption)
    | (apply StepR.snapFastfwd <;> assumption)
    | (apply StepR.snapStale <;> assumption)
    | (apply StepR.takeReads <;> assumption)
    | (apply StepR.readFwd <;> assumption)
    | (apply StepR.readPend <;> assumption)
    | (apply StepR.readArrive <;> assumption)
    | (apply StepR.readRelease <;> assumption)
    | (apply StepR.readAck <;> assumption)
    | (apply StepR.readSingle <;> assumption)
    | (apply StepR.readReleaseSingle <;> assumption)
    | (apply StepR.readState <;> assumption)
    | (apply StepR.sendFree <;> assumption)
    | (apply StepR.abandon <;> assumption)
    | (apply StepR.zeroAck <;> assumption)
    | (apply StepR.reMatch <;> assumption)
    | (apply StepR.advance <;> assumption)
    | (apply StepR.applySnap <;> assumption)
    | (apply StepR.stepDown <;> assumption)

end mono

/-! ### At a static configuration

(Until D19p, 2026-10-18, also `stepR_static`: see the file header.) -/

section static
variable [FfiSyntax]

/-- The configuration has the voters `V`, not joint. -/
def StaticR (V : GSet w64) (r : RState) : Prop :=
  r.cfg.cfg.incoming = V ∧ r.cfg.cfg.outgoing = ∅

/-- A non-follower is a voter of `V`. -/
def RoleVoter (id : w64) (V : GSet w64) (r : RState) : Prop :=
  r.p.role ≠ .follower → id ∈ V

theorem StaticR.voters {V : GSet w64} {r : RState} (h : StaticR V r) : r.cfg.cfg.voters = V := by
  rw [CfgM.voters_of_out h.2, h.1]

theorem StaticR.jquorum {V : GSet w64} {r : RState} (h : StaticR V r) (q : GSet w64) :
    JQuorum r.cfg.cfg q ↔ JQuorum (CfgM.simple V ∅) q := by
  unfold JQuorum; rw [h.1, h.2]; rfl

theorem StaticR.jlost {V : GSet w64} {r : RState} (h : StaticR V r) (votes : GMap w64 Bool) :
    JLost r.cfg.cfg votes ↔ JLost (CfgM.simple V ∅) votes := by
  unfold JLost; rw [h.1, h.2]; rfl

theorem StaticR.jquorumAcked {V : GSet w64} {r : RState} (h : StaticR V r) (f : w64 → w64)
    (N : w64) : JQuorumAcked r.cfg.cfg f N ↔ JQuorumAcked (CfgM.simple V ∅) f N := by
  unfold JQuorumAcked; simp only [h.jquorum]

theorem preadRespondAll_role (id : w64) (s : PState) (qs : List ReadReq) :
    (preadRespondAll id s qs).role = s.role := by
  obtain ⟨o, rd, h⟩ := preadRespondAll_eq id s qs
  rw [h]

end static

end EtcdGrove
end Perennial
