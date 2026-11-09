/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 3 (2026-11-09): the untraced instances of the
node-event hooks' direct callers whose specs now take the simulation's capability
(`raft.becomeFollower.spec`, `raft.becomeCandidate.spec`, `raft.maybeCommit.spec`: one spec for both
modes, through the caller's gate `HookGate`, `notes/decisions.md`, "Q8 stage 1 (slice 3)"). An untraced caller (`s.gh.tr = none`) uses the
instance here (`X.untraced`, of the statement `X.untracedTriple`), which is the spec before slice 3:
the hook's gate `HookGate none` given by the struct's nil logger (`ownRaftPhysC_traceLogger`,
`hookGate_none`), with `Q := emp`. Not specs: each is a consequence of its function's one spec, for
the callers that stay untraced (`raft.Step`'s handlers, `stepLeader`, `switchToConfig`, `newRaft`,
`RawNode.Bootstrap`, `campaign`).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.raft__becomeCandidate
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section untraced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `raft.becomeFollower.spec` at an untraced node (the statement before slice 3). -/
abbrev raft.becomeFollower.untracedTriple : Prop :=
  ∀ (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) (term lead : w64),
  uint.Z s.term ≤ uint.Z term →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeFollower"))
      (Val #term)) (Val #lead))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c V r id { becomeFollower s term lead with prvals := pvs } }}

/-- `raft.becomeFollower.spec`'s untraced instance. -/
theorem raft.becomeFollower.untraced (h : raft.becomeFollower.spec (GF := GF) (hG := hG)) :
    raft.becomeFollower.untracedTriple (GF := GF) (hG := hG) := by
  intro c V r id s term lead hle htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Hok, Hphys⟩
  iapply h c r id s term lead iprop(emp) hle (fun h' => absurd htr h') $$ [Hphys]
  · iframe Hpkg Hphys
    rw [htr]
    iapply hookGate_none r _ tl iprop(emp) Hok
    iframe Htl
  inext
  iintro %pvs ⟨Hphys, -⟩
  iapply HΦ $$ %pvs
  iexact Hphys

/-- `raft.becomeCandidate.spec` at an untraced node. -/
abbrev raft.becomeCandidate.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .leader →
  uint.Z s.term + 1 < 2 ^ 64 →
  id ∈ c.voters →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeCandidate")) (Val #()))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { becomeCandidate id s with prvals := pvs } }}

/-- `raft.becomeCandidate.spec`'s untraced instance. -/
theorem raft.becomeCandidate.untraced (h : raft.becomeCandidate.spec (GF := GF) (hG := hG)) :
    raft.becomeCandidate.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s hrole hnw hid htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Hok, Hphys⟩
  iapply h c r id s iprop(emp) hrole hnw hid $$ [Hphys]
  · iframe Hpkg Hphys
    rw [htr]
    iapply hookGate_none r _ tl iprop(emp) Hok
    iframe Htl
  inext
  iintro %pvs ⟨Hphys, -⟩
  iapply HΦ $$ %pvs
  iexact Hphys

/-- `raft.maybeCommit.spec` at an untraced node. -/
abbrev raft.maybeCommit.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeCommit")) (Val #()))
  {{ (b : Bool) (N : w64), RET #b;
      ownRaftPhysCV c c.voters r id
        (if b then { s with logst := { s.logst with committed := N } } else s) ∗
      ⌜b = true → CommitOkC c (toPState s) N⌝ }}

/-- `raft.maybeCommit.spec`'s untraced instance. -/
theorem raft.maybeCommit.untraced (h : raft.maybeCommit.spec (GF := GF) (hG := hG)) :
    raft.maybeCommit.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s hlead htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Hok, Hphys⟩
  iapply h c r id s (fun _ _ => iprop(emp)) hlead $$ [Hphys]
  · iframe Hpkg Hphys
    iintro %b %N %-
    rw [htr]
    iapply hookGate_none r _ tl iprop(emp) Hok
    iframe Htl
  inext
  iintro %b %N ⟨-, Hphys, %HN, -⟩
  iapply HΦ $$ %b %N
  iframe Hphys
  ipureintro; exact HN

end untraced

end EtcdGrove
end Perennial
