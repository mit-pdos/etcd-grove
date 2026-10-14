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
it is implied by the decoder); the static one (`StaticAdm V`) the voters `V` unchanged, under
which `StepR` projects to `StepC` (`stepR_static`) and so refines the ghost state as `StepC`
does (`ownRaftGhost_stepR`, `RefinementR.lean`). `StepR.mono`: a derivation under `Adm` is
one under any weaker `Adm'`.

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
  fp : List raftpb.Entry

/-- The node's full log, from `base0`: the entry at log index `i` is at position `i - 1`. -/
def RState.full (r : RState) : List raftpb.Entry := r.fp ++ r.p.log

/-- No conf-change entry at the positions `[lo, hi)` of `l` (log indices `(lo, hi]`). -/
def NoConfIn (l : List raftpb.Entry) (lo hi : Nat) : Prop :=
  ∀ (k : Nat) (e : raftpb.Entry), lo ≤ k → k < hi → l[k]? = some e → ¬ IsConfEnt e

/-- An `MsgApp` carries the sender's commit index (Go's `sendAppend`). -/
def AppCommitEq (s : PState) (m : Msg) : Prop := m.ty = .app → m.commit = s.commit

/-- `stepLeader`'s conf-change loop at `r`: the batch and the new `pendingConfIndex`. -/
def propBatch (r : RState) (ents : List raftpb.Entry) (cs : List (Option CCMsg)) :
    List raftpb.Entry × w64 :=
  propConf r.applied (plastIndex r.p) r.pci ents cs (CfgM.joint r.cfg.cfg)

/-- The dynamic model's configurations: the fold of the prefix from `c0` (A3). -/
def AdmFold (dec : CCDec) (c0 : CCState) (l : List raftpb.Entry) (cs : CCState) : Prop :=
  cfgFold dec c0 l = some cs

/-- The static model's configurations: voters `V`, not joint (learners free). -/
def StaticAdm (V : GSet w64) (_ : List raftpb.Entry) (cs : CCState) : Prop :=
  cs.cfg.incoming = V ∧ cs.cfg.outgoing = ∅

end state

section model
variable [FfiSyntax]

variable (Adm : List raftpb.Entry → CCState → Prop) (dec : CCDec) (id : w64)

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
      plogLastIndexZ r.p.base r.p.log + 1 < 2 ^ 64 →
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
  | appAccept (m : Msg) (r : RState) (lastnewi : w64) (es' : List raftpb.Entry) :
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
      plogLastIndexZ r.p.base r.p.log + (m.entries.length : Int) < 2 ^ 64 →
      StepR r [m] { r with
        p := psendMsgs
          (pappend r.p ((propBatch r m.entries cs).1.mapIdx (stamp r.p.term (plastIndex r.p))))
          [pselfAck id (pappend r.p
            ((propBatch r m.entries cs).1.mapIdx (stamp r.p.term (plastIndex r.p))))]
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
  | snapRestore (m : Msg) (r : RState) (fp' : List raftpb.Entry) (cs' : CCState) :
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
  | readPend (m : Msg) (r : RState) (pm : raftpb.Message) :
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
  | readAck (m : Msg) (r : RState) (N : w64) :
      m.ty = .heartbeatResp → m.dst = id → m.term = r.p.term → r.p.role = .leader →
      m.ctx ≠ [] →
      JQuorumAcked r.cfg.cfg
        (fun v => ((readonlyRecvAck r.p.rd.ro m.src m.ctx).acks !! v).getD (W64 0)) N →
      StepR r [m] { r with p := (preadRespondAll id
        ({ r.p with rd := { r.p.rd with
             ro := (readonlyAdvance (readonlyRecvAck r.p.rd.ro m.src m.ctx) N).1 } })
        (readonlyAdvance (readonlyRecvAck r.p.rd.ro m.src m.ctx) N).2) }
  | readState (m : Msg) (r : RState) (e : raftpb.Entry) :
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
  | applyConf (r : RState) (k : Nat) (e : raftpb.Entry) (op : CCOp) (cs' : CCState) :
      r.snap = false →
      r.cidx ≤ k →
      k < uint.nat r.p.commit →
      r.full[k]? = some e →
      IsConfEnt e →
      NoConfIn r.full r.cidx k →
      dec (r.full.take k) e = some op →
      ccStepB op r.cfg = some cs' →
      Adm (r.full.take (k + 1)) cs' →
      StepR r [] { r with cidx := k + 1, cfg := cs' }
  /-- `switchToConfig` with `StepDownOnRemoval`: a leader outside the voters steps down at its
  term. -/
  | stepDown (r : RState) :
      r.p.role = .leader →
      id ∉ r.cfg.cfg.voters →
      StepR r [] { r with p := pbecomeFollower r.p r.p.term (W64 0), pci := W64 0 }

end model

/-! ### Monotonicity in the admissible configurations -/

section mono
variable [FfiSyntax]

theorem StepR.mono {Adm Adm' : List raftpb.Entry → CCState → Prop} {dec : CCDec} {id : w64}
    (hA : ∀ l cs, Adm l cs → Adm' l cs) {r : RState} {ms : List Msg} {r' : RState}
    (h : StepR Adm dec id r ms r') : StepR Adm' dec id r ms r' := by
  induction h with
  | refl r => exact .refl r
  | trans _ _ _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ _ _ ih1 ih2
  | snapRestore m r fp' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .snapRestore m r fp' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 (hA _ _ h10)
  | applyConf r k e op cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .applyConf r k e op cs' h1 h2 h3 h4 h5 h6 h7 h8 (hA _ _ h9)
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
    | (apply StepR.readState <;> assumption)
    | (apply StepR.sendFree <;> assumption)
    | (apply StepR.abandon <;> assumption)
    | (apply StepR.zeroAck <;> assumption)
    | (apply StepR.reMatch <;> assumption)
    | (apply StepR.advance <;> assumption)
    | (apply StepR.applySnap <;> assumption)
    | (apply StepR.stepDown <;> assumption)

end mono

/-! ### At a static configuration, `StepR` is `StepC`

With the voters fixed at `V` (`StaticAdm V`: every configuration a node takes on has them,
learners free), a `StepR` derivation from a state at `V` whose non-follower is a voter
(`RoleVoter`, the code's `Hvoter`) is a `StepC (CfgM.simple V ∅)` derivation of its protocol
states: the new rules are stuttering steps (`advance`, `applySnap`, `applyConf`, `propDrop`
change no `PState`), `stepDown` cannot fire (a leader is a voter), and the guards and the
exact proposal loop only strengthen `StepC`'s premises (`propConf_repl`). -/

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

theorem stepR_static {V : GSet w64} {dec : CCDec} {id : w64} {r : RState} {ms : List Msg}
    {r' : RState} (h : StepR (StaticAdm V) dec id r ms r') (hs : StaticR V r)
    (hv : RoleVoter id V r) :
    StepC (CfgM.simple V ∅) id r.p ms r'.p ∧ StaticR V r' ∧ RoleVoter id V r' := by
  induction h with
  | refl r => exact ⟨.refl _, hs, hv⟩
  | trans _ _ _ _ _ _ _ ih1 ih2 =>
    obtain ⟨h1, hs1, hv1⟩ := ih1 hs hv
    obtain ⟨h2, hs2, hv2⟩ := ih2 hs1 hv1
    exact ⟨.trans _ _ _ _ _ h1 h2, hs2, hv2⟩
  | higherTerm m r h1 h2 h3 =>
    exact ⟨.higherTerm m r.p h1 h2 h3, hs, fun h => absurd rfl h⟩
  | campaign r peers cl h1 h2 _ _ h5 h6 =>
    rw [hs.voters] at h2 h6
    refine ⟨.campaign r.p peers cl h1 (by rw [CfgM.voters_simple]; exact h2) h5
      (by rw [CfgM.voters_simple]; exact h6), hs, fun _ => h2⟩
  | win r mt ms h1 h2 h3 h4 h5 _ =>
    exact ⟨.win r.p mt ms h1 ((hs.jquorum _).1 h2) h3 h4 h5, hs,
      fun _ => hv (by rw [h1]; intro h; cases h)⟩
  | lose r h1 h2 =>
    exact ⟨.lose r.p h1 ((hs.jlost _).1 h2), hs, fun h => absurd rfl h⟩
  | commit r n h1 h2 h3 h4 h5 =>
    exact ⟨.commit r.p n h1 h2 h3 h4 ((hs.jquorum _).1 h5), hs, hv⟩
  | readAck m r N h1 h2 h3 h4 h5 h6 =>
    refine ⟨.readAck m r.p N h1 h2 h3 h4 h5 ((hs.jquorumAcked _ _).1 h6), hs, ?_⟩
    intro h; apply hv
    simp only [preadRespondAll_role] at h
    exact h
  | propose m r cs h1 h2 h3 h4 =>
    have hrep := propConf_repl (joint := CfgM.joint r.cfg.cfg) r.applied (plastIndex r.p) r.pci
      m.entries cs h3
    have hlen := hrep.length
    refine ⟨.propose m r.p _ h1 hrep h2 (by unfold propBatch; rw [hlen]; exact h4), hs, hv⟩
  | propDrop => exact ⟨.refl _, hs, hv⟩
  | snapRestore m r fp' cs' h1 h2 h3 h4 h5 h6 h7 _ _ h10 =>
    exact ⟨.snapRestore m r.p h1 h2 h3 h4 h5 h6 h7, h10, fun h => absurd rfl h⟩
  | advance => exact ⟨.refl _, hs, hv⟩
  | applySnap => exact ⟨.refl _, hs, hv⟩
  | applyConf r k e op cs' _ _ _ _ _ _ _ _ h9 => exact ⟨.refl _, h9, hv⟩
  | stepDown r h1 h2 =>
    exact absurd (by rw [hs.voters]; exact hv (by rw [h1]; intro h; cases h)) h2
  | _ =>
    refine ⟨?_, hs, ?_⟩
    · first
      | (apply StepC.grantVote <;> assumption)
      | (apply StepC.rejectVote <;> assumption)
      | (apply StepC.recordVote <;> assumption)
      | (apply StepC.drain <;> assumption)
      | (apply StepC.appAccept <;> assumption)
      | (apply StepC.appStale <;> assumption)
      | (apply StepC.appReject <;> assumption)
      | (apply StepC.heartbeat <;> assumption)
      | (apply StepC.beat <;> assumption)
      | (apply StepC.appResp <;> assumption)
      | (apply StepC.sendApps <;> assumption)
      | (apply StepC.propForward <;> assumption)
      | (apply StepC.snapFastfwd <;> assumption)
      | (apply StepC.snapStale <;> assumption)
      | (apply StepC.takeReads <;> assumption)
      | (apply StepC.readFwd <;> assumption)
      | (apply StepC.readPend <;> assumption)
      | (apply StepC.readArrive <;> assumption)
      | (apply StepC.readRelease <;> assumption)
      | (apply StepC.readState <;> assumption)
      | (apply StepC.sendFree <;> assumption)
      | (apply StepC.abandon <;> assumption)
      | (apply StepC.zeroAck <;> assumption)
      | (apply StepC.reMatch <;> assumption)
    · first
      | exact hv
      | exact fun h => absurd rfl h

end static

end EtcdGrove
end Perennial
