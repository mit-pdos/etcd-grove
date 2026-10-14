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
variable [FfiSyntax]

/-- A3 on a `ConfState`: well formed, and denoting the configuration of the prefix `pre`. -/
def SnapConfOk (dec : CCDec) (c0 : CCState) (pre : List raftpb.Entry)
    (vo v l ln : List w64) (al : Bool) : Prop :=
  CSWf vo v l ln ∧ ∃ s, cfgFold dec c0 pre = some s ∧ csCfgM vo v l ln al = s.cfg

/-- The application's obligation on a snapshot at index `i` with that `ConfState`, the
application having applied the entries `applied` (from index 1): the snapshot is of an applied
prefix, and its `ConfState` is that prefix's configuration. -/
def SnapObl (dec : CCDec) (c0 : CCState) (applied : List raftpb.Entry) (i : w64)
    (vo v l ln : List w64) (al : Bool) : Prop :=
  uint.nat i ≤ applied.length ∧
  SnapConfOk dec c0 (applied.take (uint.nat i)) vo v l ln al

/-- The states a fold reaches from a reachable one are reachable (`CCGood`). -/
theorem cfgFoldFrom_good {dec : CCDec} {pre : List raftpb.Entry} {s s' : CCState}
    {l : List raftpb.Entry} (h : CCGood s) (H : cfgFoldFrom dec pre s l = some s') :
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

theorem cfgFold_good {dec : CCDec} {c0 s : CCState} {l : List raftpb.Entry} (h : CCGood c0)
    (H : cfgFold dec c0 l = some s) : CCGood s :=
  cfgFoldFrom_good h H

/-- A reachable state is what `confchange` sees of its configuration. -/
theorem cfgStateC_of_good {s : CCState} (h : CCGood s) : cfgStateC s.cfg = s := by
  cases s with
  | mk c f =>
    unfold cfgStateC
    rw [CCGood.flags h]

/-- `Restore` of a `ConfState` that A3 holds of answers the prefix's configuration. -/
theorem SnapConfOk.restoreM_eq {dec : CCDec} {c0 : CCState} {pre : List raftpb.Entry}
    {vo v l ln : List w64} {al : Bool} (H : SnapConfOk dec c0 pre vo v l ln al)
    (Hg : CCGood c0) :
    ∃ s, cfgFold dec c0 pre = some s ∧ restoreM vo v l ln al = some s := by
  obtain ⟨Hwf, s, Hf, Hc⟩ := H
  refine ⟨s, Hf, ?_⟩
  rw [restoreM_wf vo v l ln al Hwf, Hc, cfgStateC_of_good (cfgFold_good Hg Hf)]

/-- The obligation gives the snapshot's index within the applied entries and `Restore`'s
answer, the configuration of the applied prefix up to it. -/
theorem SnapObl.restoreM_eq {dec : CCDec} {c0 : CCState} {applied : List raftpb.Entry}
    {i : w64} {vo v l ln : List w64} {al : Bool} (H : SnapObl dec c0 applied i vo v l ln al)
    (Hg : CCGood c0) :
    uint.nat i ≤ applied.length ∧ ∃ s, cfgFold dec c0 (applied.take (uint.nat i)) = some s ∧
      restoreM vo v l ln al = some s :=
  ⟨H.1, H.2.restoreM_eq Hg⟩

end model

end EtcdGrove
end Perennial
