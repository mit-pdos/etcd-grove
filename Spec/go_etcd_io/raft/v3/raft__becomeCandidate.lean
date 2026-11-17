/-
Port of election_proof/spec_raft__becomeCandidate.v (feb5c73d4).

Lean notes:
* Rocq's `pvs` is untyped; its type is `GMap w64 Progress`, that of `NState.prvals`.
  `prole.Leader` is `PRole.leader`.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap

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

/-- `becomeCandidate` is `reset` plus the role transition; the panic branch
(`state = StateLeader`) is discharged from the role hypothesis. The new term `r.Term + 1`
does not wrap (2026-10-10: `reset`'s term does not move back; `campaign` has it).

One spec for both modes (Q8 stage 1, slice 3, 2026-11-09; `notes/decisions.md`, "Q8 stage 1 (slice
3)"): the hook `traceBecomeCandidate` logs the `BecomeCandidate` line of the new state, through the
caller's gate `HookGate s.gh.tr r E Q` (an update at the hook giving the logger and `TraceFire`),
given back as `Q`. A traced caller gives it from the simulation's capability, by the line's law
(`trCapB_hookGate`, with the line's phase step and facts: `raft.becomeCandidate.traced`, `TracedHooks.lean`);
an untraced one (`s.gh.tr = none`) from the struct's nil logger (`raft.becomeCandidate.untraced`).
Until slice 3 the premise `s.gh.tr = none`. -/
abbrev raft.becomeCandidate.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (Q : IProp GF),
  s.role ≠ .leader →
  uint.Z s.term + 1 < 2 ^ 64 →
  -- (2026-10-13) only a voter campaigns (`ownRaftPhys`'s `Hvoter`)
  id ∈ c.voters →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      -- (Q8 stage 1, slice 3) the `BecomeCandidate` line's gate, the caller's
      HookGate s.gh.tr r (NodeEvOf (W64 1) id (becomeCandidate id s) c) Q }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeCandidate")) (Val #()))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { becomeCandidate id s with prvals := pvs } ∗ Q }}

end spec

end EtcdGrove
end Perennial
