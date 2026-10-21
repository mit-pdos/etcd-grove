/-
Pure definitions that the model-level lemmas (`StepLemmasR`, `StepGhostMode`) name and that the
old proof kept in files with heap facts (raft v3.7 retarget, stage R1). Moved here verbatim (with
R1's type rename), so that those lemmas port without the physical predicates; the files they
came from, ported with the log and raft layers (stages R3/R4), import this one and drop them:

* from `InvReadylog.lean`: the message type `MsgStorageApplyResp` and the local threads'
  ids `LocalAppendThread`, `LocalApplyThread`;
* from `InvRaftlog.lean`: `scanRange` and `unappliedEnts` (the entries `scan` pages through,
  the committed entries not applied yet);
* from `Spec/go_etcd_io/raft/v3/raft__hup.lean`, its `section results`: `HupOk`, `HupGuard`,
  `HupOkC` (what `hup` leaves and checked), `HupOkC.simple`;
* from `Spec/go_etcd_io/raft/v3/raft__restore.lean`, its `section results`: `SnapScope`,
  `CSLists.Has`, `snapCfg`, `RestoreResult`, `restoreCfg` (stated on the snapshot's record
  `SnapshotM` instead of the Goose value `raftpb.Snapshot`; they read the same fields,
  `sv.Metadata'.Index'`, `sv.Metadata'.ConfState'.AutoLeave'`). See that spec file's header for
  what they mean.
-/
module

public import Proof.go_etcd_io.raft.v3.StepLemmasC
public import Proof.go_etcd_io.raft.v3.InvRestore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

def MsgStorageApplyResp : w32 := W32 22
def LocalAppendThread : w64 := W64 18446744073709551615
def LocalApplyThread : w64 := W64 18446744073709551614

section scan
variable [FfiSyntax]

/-- The entries `scan lo hi` pages through: the log's at `[lo, hi)`. -/
def scanRange (ls : LogState) (lo hi : w64) : List EntryM :=
  (plogFrom ls.prev (ls.sents ++ ls.uents) lo).take (uint.Z hi - uint.Z lo).toNat

/-- The committed entries not applied yet (2026-10-13): the log's at
`(applied, committed]`, which `hasUnappliedConfChanges` scans. -/
def unappliedEnts (ls : LogState) : List EntryM :=
  scanRange ls (ls.applied + W64 1) (ls.committed + W64 1)

end scan

/-! ## `hup`'s results (`Spec/go_etcd_io/raft/v3/raft__hup.lean`) -/

section hup_results
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- What `hup` checked before it campaigned (2026-10-14, reconfiguration stage B7: the dynamic
model's `StepR.campaign` guard): nothing done, or a campaign (`campaignState`) by a non-leader
voter of either half, with no snapshot pending (`promotable`) and no conf-change entry committed
but not applied (`hasUnappliedConfChanges`), asking every other voter. -/
def HupGuard (c : CfgM) (id : w64) (s s' : NState) : Prop :=
  s' = s ∨
  (s.role ≠ .leader ∧ id ∈ c.voters ∧ s.logst.snap = none ∧
   (¬ ∃ e ∈ unappliedEnts s.logst, IsConfEnt e) ∧
   ∃ (pre : Bool) (peers : List w64) (pvs : GMap w64 Progress) (cl : List w8),
     peers ≡ₚ elements (c.voters \ {[id]}) ∧
     s' = { campaignState id s pre peers cl with prvals := pvs })

/-- What `hup` leaves (its postcondition's pure part, 2026-10-13, for `stepFollower`'s
`MsgTimeoutNow`), at a joint configuration (2026-10-13, reconfiguration stage A2): `r.step` agrees
with the role, a `StepC c` step that receives nothing, the log untouched, the term up by at most
one (a step at every bound `B`: it creates no entry), `r.preVote` and the ghost bounds kept; a
node that is not a voter of either half does nothing (it is not `promotable`). (2026-10-14,
stage B7) And what `hup` checked (`HupGuard`). (Until 2026-10-21 also `HupOk`, at a simple
configuration and the old `Step` model.) -/
def HupOkC (c : CfgM) (id : w64) (s s' : NState) : Prop :=
  NStateWf s' ∧ (∀ B, StepC c id B (toPState s) [] (toPState s')) ∧
  (s'.logst = s.logst ∧ uint.Z s.term ≤ uint.Z s'.term ∧
   uint.Z s'.term ≤ uint.Z s.term + 1 ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh) ∧
  (id ∉ c.voters → s' = s) ∧ HupGuard c id s s'

/-- (2026-10-17) After `hup`, a pre-candidate is at the term it was at (a pre-campaign keeps the
term; an election raises it, but makes a candidate). -/
theorem HupGuard.precand {c : CfgM} {id : w64} {s s' : NState} (h : HupGuard c id s s')
    (hp : s'.role = .preCandidate) : s'.term = s.term := by
  rcases h with rfl | ⟨-, -, -, -, pre, peers, pvs, cl, -, rfl⟩
  · rfl
  · cases pre
    · simp [campaignState, sendMsgs, becomeCandidate] at hp
    · simp [campaignState, sendMsgs, becomePrecandidate]

end hup_results

/-! ## `restore`'s results (`Spec/go_etcd_io/raft/v3/raft__restore.lean`) -/

section restore_results
variable [FfiSyntax]

/-- The scope for a snapshot's `ConfState`; see the file header. -/
def SnapScope (sv : SnapshotM) (cl : CSLists) : Prop :=
  let cs := sv.Metadata'.ConfState'
  CSWf cl.outgoing cl.voters cl.learners cl.learnersNext ∧
  cl.voters.Nodup ∧ cl.learners.Nodup ∧ cl.outgoing.Nodup ∧ cl.learnersNext.Nodup ∧
  (cl.voters.length + cl.learners.length + cl.outgoing.length + cl.learnersNext.length : Int)
    ≤ 2 ^ 62 ∧
  (cl.outgoing = [] → cs.AutoLeave' = false) ∧
  uint.Z sv.Metadata'.Index' < 2^61

/-- `id` is in one of the sets `restore`'s `found` search reads: an incoming voter, a learner or
an outgoing voter (2026-10-14, reconfiguration stage B8; a staged learner is an outgoing voter,
`CSWf`). -/
def CSLists.Has (cl : CSLists) (id : w64) : Prop :=
  id ∈ cl.voters ∨ id ∈ cl.learners ∨ id ∈ cl.outgoing

/-- The configuration a snapshot's `ConfState` denotes (2026-10-14, reconfiguration stage B8). -/
abbrev snapCfg (sv : SnapshotM) (cl : CSLists) : CfgM :=
  csCfgM cl.outgoing cl.voters cl.learners cl.learnersNext sv.Metadata'.ConfState'.AutoLeave'

/-- The three exits of `restore`; see the file header. -/
def RestoreResult (s : NState) (sv : SnapshotM) (cl : CSLists) (b : Bool) (s' : NState) :
    Prop :=
  let ls := s.logst
  let es := ls.sents ++ ls.uents
  let sid := snapId sv
  (uint.Z sid.index' ≤ uint.Z ls.committed ∧
   b = false ∧ s' = s)
  ∨
  (uint.Z ls.committed < uint.Z sid.index' ∧
   PlogMatches ls.prev es sid ∧ b = false ∧
   s' = { s with logst := { ls with committed := sid.index' } })
  ∨
  (uint.Z ls.committed < uint.Z sid.index' ∧
   ¬ PlogMatches ls.prev es sid ∧ b = true ∧
   ∃ prs pvs il, s' = { s with progress := prs, prvals := pvs,
                               logst := logRestore ls (snapTrip sv cl), isLearner := il })

/-- The configuration the node is at after `restore` (2026-10-14, reconfiguration stage A3; the
snapshot's any `ConfState`'s since B8): the snapshot's when it restored (`b`), the one it was
at otherwise. -/
def restoreCfg (c : CfgM) (sv : SnapshotM) (cl : CSLists) (b : Bool) : CfgM :=
  if b then snapCfg sv cl else c

end restore_results

end EtcdGrove
end Perennial
