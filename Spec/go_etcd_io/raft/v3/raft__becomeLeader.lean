/- Port of election_proof/spec_raft__becomeLeader.v (feb5c73d4).

Lean notes: Rocq's `become_leader id s <| nstate.prvals := pvs |>` is
`{ becomeLeader id s with prvals := pvs }`, and the type of the untyped binder `pvs` is
written out.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `becomeLeader` is `reset`, the role transition, marking its own `Progress`
replicating, and the empty entry, which `appendEntry` acknowledges with a
self-addressed `MsgAppResp` (`becomeLeader`, `Defs.lean`). It dereferences
`r.trk.Progress[r.id]`, so the node's own `Progress` must be there: since 2026-10-13
(reconfiguration stage A2, at any configuration `c`) that is not a premise, it follows from
`ownRaftPhysC`'s `Hvoter` -- a non-follower is a voter of either half, and every voter is
tracked (`CfgM.ids`). (The old statement, `raft.becomeLeader.specS`, took `id ∈ cfg`; it had no caller and is gone, 2026-10-17.) The term is nonzero (2026-10-10): `appendEntry`
stamps the self-acknowledgement with it (a candidate's term, which `stepCandidate` has
from the winning `MsgVoteResp`). -/
abbrev raft.becomeLeader.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .follower →
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeLeader")) (Val #()))
  {{ (pvs : GMap w64 Progress), RET #();
      -- (2026-10-20, witness support) at the reset epoch (`maybeStartNewSubterm`: subterm 0,
      -- the witness excluded)
      ownRaftPhysCV c c.voters r id
        { becomeLeader id s with prvals := pvs,
                                 ep := resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0) } ∗
      -- `Match` is what `reset` left: `BecomeReplicate` and the `RecentActive` store do
      -- not move it, and `appendEntry` does not touch a `Progress`
      ⌜prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals⌝ }}

end spec

end EtcdGrove
end Perennial
