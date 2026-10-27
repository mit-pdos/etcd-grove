/-
The application's obligation on the snapshots it makes (A3 of notes/reconfiguration-safety.md),
as pure definitions a spec can take as a premise (2026-10-14, reconfiguration stage B8).

A3: a snapshot's `ConfState` is the configuration of the log prefix it covers, and the snapshot
covers no more than the application has applied. The application makes a snapshot with
`MemoryStorage.CreateSnapshot(i, cs, data)` (or installs one with `ApplySnapshot`); raft hands
it to the followers (`maybeSendSnapshot`, from `Storage.Snapshot()`) and a follower restores
its configuration from the `ConfState` (`raft.restore`, `confchange.Restore`). What the storage
keeps of it is in `Spec/go_etcd_io/raft/v3/MemoryStorage__*.lean` (the `ConfState` stored and
returned as given); what `Restore` makes of it is `restoreM` (`InvRestore.lean`).

* `SnapConfOk dec c0 pre vo v l ln al`: the `ConfState` with `VotersOutgoing = vo`, `Voters =
  v`, `Learners = l`, `LearnersNext = ln`, `AutoLeave = al` is well formed (`CSWf`) and denotes
  (`csCfgM`) the configuration `cfgFold dec c0 pre` of the entries `pre` (the log from index 1
  up to the snapshot's index), from the initial configuration `c0`, conf entries decoded by
  `dec` (`CfgOverlap.lean`). This is B5's `AdmFold` read on a `ConfState`.
* `SnapObl dec c0 applied i ...`: the obligation on a snapshot at index `i`, for an application
  that has applied the entries `applied` (from index 1, in order): `i ≤ |applied|` (the
  snapshot's index is at most the applied index) and `SnapConfOk` of the first `i`.
* `SnapConfOk.restoreM_eq`: then `Restore` of that `ConfState` answers exactly the fold's state
  (`restoreM ... = some s`), given `CCGood c0` (true of every configuration raft builds;
  `cfgFold_good`).

The lists are the contents of the `ConfState`'s slices (`cs.Voters' ↦* v`, `ownIdList
cs.Learners' _ l`, ...), which the specs relate to the Go value; `al` is `cs.AutoLeave'`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRestore
public import Proof.go_etcd_io.raft.v3.Protocol.CfgOverlap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section model
variable [GooseExts]

/-- A3 on a `ConfState`: well formed, and denoting the configuration of the prefix `pre`. -/
def SnapConfOk (dec : CCDec) (c0 : CCState) (pre : List EntryM)
    (vo v l ln : List w64) (al : Bool) : Prop :=
  CSWf vo v l ln ∧ ∃ s, cfgFold dec c0 pre = some s ∧ csCfgM vo v l ln al = s.cfg

/-- The states a fold reaches from a reachable one are reachable (`CCGood`). -/
theorem cfgFoldFrom_good {dec : CCDec} {pre : List EntryM} {s s' : CCState}
    {l : List EntryM} (h : CCGood s) (H : cfgFoldFrom dec pre s l = some s') :
    CCGood s' := by
  induction l generalizing pre s with
  | nil => simp only [cfgFoldFrom, Option.some.injEq] at H; subst H; exact h
  | cons e es ih =>
    simp only [cfgFoldFrom] at H
    cases h1 : entStep dec pre s e with
    | none => rw [h1] at H; cases H
    | some s1 =>
      rw [h1] at H
      refine ih ?_ H
      unfold entStep at h1
      split at h1
      · cases h2 : dec pre e with
        | none => rw [h2] at h1; cases h1
        | some op =>
          rw [h2] at h1
          simp only [Option.bind_some, ccStepB] at h1
          cases h3 : ccApplyM op.1 op.2 s with
          | none => rw [h3] at h1; cases h1
          | some s2 =>
            rw [h3] at h1
            simp only [Option.bind_some] at h1
            split at h1
            · cases h1; exact ccApplyM_good h op.1 op.2 h3
            · cases h1
      · cases h1; exact h

theorem cfgFold_good {dec : CCDec} {c0 s : CCState} {l : List EntryM} (h : CCGood c0)
    (H : cfgFold dec c0 l = some s) : CCGood s :=
  cfgFoldFrom_good h H

/-- A reachable state is what `confchange` sees of its configuration. -/
theorem cfgStateC_of_good {s : CCState} (h : CCGood s) : cfgStateC s.cfg = s := by
  cases s with
  | mk c f =>
    unfold cfgStateC
    rw [CCGood.flags h]

end model

/-! ### The certificate, stated on the ghost records (2026-10-15, stage S)

`raftSnapCert γ k` is what a receiver of a `MsgSnap` needs of the snapshot `k` (id, lists,
`AutoLeave`; `SnapTrip`, `Defs.lean`): `SnapScope`'s facts (`SnapListsOk`), and what the mode asks
(`GMode.SnapOk`, `StepGhostMode.lean`): statically the ghost state's voters, not joint;
dynamically A3 for any recorded full-log prefix ending at the snapshot's id. It is persistent and
names no node, so whoever holds it may hand it along. The storage records which lists its snapshot
has (`StorState.scs`, `sal`) and raft which certified snapshots it may send (`LogState.ksn`); what
is not done yet is carrying the certificate from those records to the receiving `raft.Step`
(notes/STATUS.md, "Snapshots at the public API (stage S)"). -/

section cert
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF]

-- (D22 S-b′3, 2026-10-20) `SnapListsOk`, `SnapTrip.cfgM` and `raftSnapCert` are
-- `Protocol/Ghost.lean`'s

end cert

end EtcdGrove
end Perennial
