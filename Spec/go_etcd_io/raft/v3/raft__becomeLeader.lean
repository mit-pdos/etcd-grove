/- Port of election_proof/spec_raft__becomeLeader.v (feb5c73d4).

Lean notes: Rocq's `become_leader id s <| nstate.prvals := pvs |>` is
`{ becomeLeader id s with prvals := pvs }`, and the type of the untyped binder `pvs` is
written out.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.TracedSend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `becomeLeader` is `reset`, the role transition, marking its own `Progress`
replicating, and the empty entry, which `appendEntry` acknowledges with a
self-addressed `MsgAppResp` (`becomeLeader`, `Defs.lean`). It dereferences
`r.trk.Progress[r.id]`, so the node's own `Progress` must be there: since 2026-10-13
(reconfiguration stage A2, at any configuration `c`) that is not a premise, it follows from
`ownRaftPhysC`'s `Hvoter` -- a candidate is a voter of either half (2026-10-25: a leader need not
be, hence the premise that the node is none), and every voter is
tracked (`CfgM.ids`). (The old statement, `raft.becomeLeader.specS`, took `id ∈ cfg`; it had no caller and is gone, 2026-10-17.) The term is nonzero (2026-10-10): `appendEntry`
stamps the self-acknowledgement with it (a candidate's term, which `stepCandidate` has
from the winning `MsgVoteResp`). 
**One spec for both trace modes** (2026-11-09, trace-check Q8 stage 1 slice 6): the caller's resource
through the three hook gates in turn, `G` to `G1` to `G2` to `G3` (each line may move the caller's
state, as the capability's phase): the `BecomeLeader` line's (`HookGate`, of the state
`becomeLeaderPre`, before the empty entry: Go traces then), the empty entry's `Replicate` line
(`appendEntry`'s `HookGateN`, one event) and the self-acknowledgement's (at `becomeLeaderLog`, the
entry appended). A traced caller's `BecomeLeader` gate is where the line's `FxPresU` creates the new
leader's term log (the plan's round 5, E1: absent before the step, present after), its `Replicate`
gate where the entry's record is created (round 6, F1). Until slice 6 the premise `s.gh.tr = none`
(stage 0), now `raft.becomeLeader.untraced`'s (`TracedUntracedSend.lean`). -/
abbrev raft.becomeLeader.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (G G1 G2 G3 : IProp GF),
  s.role ≠ .follower →
  -- (2026-10-25, T-M M2c) a candidate's (`stepCandidate`): a leader need not be a voter
  s.role ≠ .leader →
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      -- (2026-11-09, Q8 stage 1 slice 6; until then, stage 0, the premise `s.gh.tr = none`) the
      -- caller's resource, through the gates below
      "HG" ∷ G ∗
      -- the `BecomeLeader` line's gate, of the state before the empty entry
      "Hgbl" ∷ (G -∗ HookGate s.gh.tr r (NodeEvOf (W64 3) id (becomeLeaderPre id s) c) G1) ∗
      -- the empty entry's `Replicate` line's gate (`appendEntry`'s)
      "Hgrep" ∷ (G1 -∗ HookGateN s.gh.tr r (NodeEvOf (W64 5) id (becomeLeaderPre id s) c) 1 G2) ∗
      -- the self-acknowledgement's gate, at the state with the entry appended (`appendEntry`'s)
      "Hgack" ∷ (G2 -∗ HookGateOpt s.gh.tr r (sendOutGate id (becomeLeaderLog id s) c MsgAppResp
          [selfAck id (becomeLeaderLog id s)]) G3) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeLeader")) (Val #()))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { becomeLeader id s with prvals := pvs } ∗
      -- `Match` is what `reset` left: `BecomeReplicate` and the `RecentActive` store do
      -- not move it, and `appendEntry` does not touch a `Progress`
      ⌜prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals⌝ ∗ G3 }}

end spec

end EtcdGrove
end Perennial
