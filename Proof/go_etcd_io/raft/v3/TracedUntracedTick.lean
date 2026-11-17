/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 12 (2026-11-10): the tick functions' untraced
instances, the statements before slice 12 (stage 0's premise `s.gh.tr = none`, no gate), for
`RawNode.Tick`, which stays untraced (`notes/decisions.md`, "Q8 stage 1 (slice 12)"). From the one
spec with each `Step`'s resources `untracedR` (raft's ghost state), gates and closing wand
`stepBundle_none`, the caller's own `emp`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
public import Proof.go_etcd_io.raft.v3.TracedUntracedRaftStep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section untraced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `raft.tickElection.spec` at an untraced node (the statement before slice 12). -/
abbrev raft.tickElection.untracedTriple : Prop :=
  ∀ (c : CfgM) (md : GMode) (γ : RaftNames) (r : Loc) (id : w64) (s : NState),
  -- a campaign increments the term; `send` panics if it wraps
  uint.Z s.term + 1 < 2 ^ 64 →
  -- (2026-10-17) a pre-campaign's next term within the ceiling (`NGhost.tc`)
  (s.prevote = true → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) →
  NStateWf s →
  -- (D19i part 1) the floor at most `applied` (a campaign's `hup`)
  uint.Z s.logst.fl ≤ uint.Z s.logst.applied →
  -- (2026-10-14, stage B7 part 2) in either ghost mode (`raft.Step.spec`'s); in the dynamic one
  -- a pre-candidate's campaign guard (`GMode.Guard`; until 2026-10-25 no pre-candidate)
  md.Guard s →
  -- (2026-11-09, Q8 stage 0 of `notes/trace-validation-plan.md`) an untraced node: its trace
  -- hooks see a nil logger (`TraceLoggerOkS`)
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickElection")) (Val #()))
  {{ (s' : NState), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md c id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      -- (2026-11-01, durability stage II (m)) and the term and the vote as the model moves them
      "%Hcm" ∷ ⌜uint.Z s.logst.committed ≤ uint.Z s'.logst.committed ∧
        PVoteLe (toPState s) (toPState s')⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ }}

/-- `raft.tickElection.spec`'s untraced instance: the campaign's `Step` at `untracedR`, its gates and
closing wand from the struct's nil logger (`stepBundle_none`). -/
theorem raft.tickElection.untraced (h : raft.tickElection.spec (GF := GF) (hG := hG)) :
    raft.tickElection.untracedTriple (GF := GF) (hG := hG) := by
  intro c md γ r id s Hterm Htc Hwf Hfla Hpc htr
  iintro %Φ ⟨#Hinit, Hphys, Hghost⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  ihave ⟨Hgates, Hclose⟩ := stepBundle_none (GF := GF) γ md c r id s (tickMsg MsgHup id) [] none [] [] tl
    htr Htlok $$ Htl
  iapply h c md γ r id s (untracedR γ md c id s) (fun _ => iprop(emp)) Hterm Htc Hwf Hfla Hpc
    $$ [Hphys Hghost Hgates Hclose]
  · iframe Hinit Hphys Hghost Hgates Hclose
    iempintro
  inext
  iintro %s' H
  iapply HΦ $$ %s'
  iNamed H
  iframe Hphys Hghost
  ipureintro
  exact ⟨Hwf', Hcm, Htick⟩

/-- `raft.tickHeartbeat.spec` at an untraced node (the statement before slice 12). -/
abbrev raft.tickHeartbeat.untracedTriple : Prop :=
  ∀ (c : CfgM) (md : GMode) (γ : RaftNames) (r : Loc) (id : w64) (s : NState),
  NStateWf s →
  -- (2026-10-14, stage B7 part 2) in either ghost mode (`raft.Step.spec`'s)
  -- (2026-10-25, T-M M2b) a pre-candidate's campaign guard (until then no pre-candidate)
  md.Guard s →
  -- (2026-11-09, Q8 stage 0 of `notes/trace-validation-plan.md`) an untraced node: its trace
  -- hooks see a nil logger (`TraceLoggerOkS`)
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickHeartbeat")) (Val #()))
  {{ (s' : NState), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md c id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      -- (2026-11-01, durability stage II (m)) and the term and the vote as the model moves them
      "%Hcm" ∷ ⌜uint.Z s.logst.committed ≤ uint.Z s'.logst.committed ∧
        PVoteLe (toPState s) (toPState s')⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ }}

/-- `raft.tickHeartbeat.spec`'s untraced instance: each `Step` at `untracedR` of its state (the
heartbeat's at the state the first part left, whose trace mode is the node's: `s2.gh = s.gh`), the
caller's `emp` throughout. -/
theorem raft.tickHeartbeat.untraced (h : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    raft.tickHeartbeat.untracedTriple (GF := GF) (hG := hG) := by
  intro c md γ r id s Hwf Hpc htr
  iintro %Φ ⟨#Hinit, Hphys, Hghost⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c md γ r id s (untracedR γ md c id s) (fun _ => iprop(emp)) (fun _ => iprop(emp)) Hwf Hpc
    $$ [Hphys Hghost]
  · iframe Hinit Hphys Hghost
    isplitr
    · iempintro
    isplitr
    · iintro %_
      iapply stepBundle_none (GF := GF) γ md c r id s (tickMsg MsgCheckQuorum id) [] none [] [] tl
        htr Htlok
      iexact Htl
    isplitr
    · iintro -; imodintro; iempintro
    iintro %s1 %s2 %Hs2 -
    imodintro
    iexists untracedR γ md c id s2
    isplitr
    · iempintro
    iapply stepBundle_none (GF := GF) γ md c r id s2 (tickMsg MsgBeat id) [] none [] [] tl
      (by rw [Hs2.1]; exact htr) Htlok
    iexact Htl
  inext
  iintro %s' H
  iapply HΦ $$ %s'
  iNamed H
  iframe Hphys Hghost
  ipureintro
  exact ⟨Hwf', Hcm, Htick⟩

end untraced

end EtcdGrove
end Perennial
