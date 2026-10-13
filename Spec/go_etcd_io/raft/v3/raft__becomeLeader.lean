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
tracked (`CfgM.ids`). (The old statement, `raft.becomeLeader.specS`, took `id ∈ cfg`.) The term is nonzero (2026-10-10): `appendEntry`
stamps the self-acknowledgement with it (a candidate's term, which `stepCandidate` has
from the winning `MsgVoteResp`). -/
abbrev raft.becomeLeader.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .follower →
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysC c r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeLeader")) (Val #()))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysC c r id { becomeLeader id s with prvals := pvs } ∗
      -- `Match` is what `reset` left: `BecomeReplicate` and the `RecentActive` store do
      -- not move it, and `appendEntry` does not touch a `Progress`
      ⌜prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals⌝ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.becomeLeader.spec` by `raft.becomeLeader.spec_simple`. -/
abbrev raft.becomeLeader.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .follower →
  id ∈ cfg →
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeLeader")) (Val #()))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhys cfg r id { becomeLeader id s with prvals := pvs } ∗
      ⌜prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals⌝ }}

open Iris.ProofMode in
theorem raft.becomeLeader.spec_simple
    (H : raft.becomeLeader.spec (GF := GF) (hG := hG)) :
    raft.becomeLeader.specS (GF := GF) (hG := hG) := by
  intro cfg r id s Hrole _ Hnz
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s Hrole Hnz $$ [$Hpkg $Hphys]
  inext
  iintro %pvs ⟨Hphys, %Hm⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  iframe Hphys
  ipureintro; exact Hm

end spec

end EtcdGrove
end Perennial
