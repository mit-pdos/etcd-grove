-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/UntracedStepEnd.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (no Rocq counterpart). #33 S4 (P-raft-3, `notes/antithesis-rawnode-design.md` §2.7):
**untraced instances of the gated `Step` specs that keep the step's end state.** The untraced
instances of `TracedUntracedRaftStep.lean`/`TracedUntracedTick.lean` pass the caller's `emp` through
the closing wand (`stepBundle_none`) and so forget what the wand is told of the end state: `Step`'s
exact per-path end state (`StepEnd`) and, in the untraced scope `AckScope`, a storage
acknowledgement's (`AckEnd`). Here the caller's resource at the end state is that fact
(`StepEndOut`), so the post carries it:
- `stepBundle_end`: the gates and closing wand of one untraced `Step`, the closing resource any pure
  `Q` that `StepEndOut` implies (what a caller of any gated spec over `Step` supplies; `raft.Step`'s
  own instance of this kind is `raft.Step.untracedNs`, `RaftStepNoSnap.lean`, at the no-snapshot flag);
- `raft.tickElection.untracedEnd`, `raft.tickHeartbeat.untracedEnd`: the ticks' untraced instances
  with their `Step`s' end states (`TickElEnd`, `TickHbEnd`).
-/
module

public import KvNet.Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
public import KvNet.Proof.go_etcd_io.raft.v3.TracedUntracedRaftStep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **What an untraced `Step`'s closing wand is told of its end state** `s'`: the exact per-path end
state (`StepEnd`) and, with no automatic leave (`AckScope`), a storage acknowledgement's (`AckEnd`). -/
def StepEndOut (c : CfgM) (id : w64) (m : MessageM) (ents : List EntryM) (ctx : List w8)
    (s s' : NState) : Prop :=
  StepEnd c id m ents ctx s s' ∧ (AckScope c → AckEnd m s s')

/-- **`tickElection`'s end state**: no campaign (`s`), or its `MsgHup`'s `Step`'s. -/
def TickElEnd (c : CfgM) (id : w64) (s s' : NState) : Prop :=
  s' = s ∨ StepEndOut c id (tickMsg MsgHup id) [] [] s s'

/-- **The state after `tickHeartbeat`'s quorum check**: no check (`s`), or (check-quorum on) its
`MsgCheckQuorum`'s `Step`'s end state. -/
def TickCqEnd (c : CfgM) (id : w64) (s s1 : NState) : Prop :=
  s1 = s ∨ (s.cq = true ∧ StepEndOut c id (tickMsg MsgCheckQuorum id) [] [] s s1)

/-- **`tickHeartbeat`'s end state**: after the quorum check (`TickCqEnd`) and the transfer abort
(`lt := 0`), no heartbeat, or a leader's `MsgBeat`'s `Step`'s end state from there. -/
def TickHbEnd (c : CfgM) (id : w64) (s s' : NState) : Prop :=
  (∃ s1, TickCqEnd c id s s1 ∧ (s' = s1 ∨ s' = { s1 with lt := W64 0 })) ∨
  (∃ s1 s2, TickCqEnd c id s s1 ∧ s2.gh = s.gh ∧ s2.role = .leader ∧
    (s2 = s1 ∨ s2 = { s1 with lt := W64 0 }) ∧ StepEndOut c id (tickMsg MsgBeat id) [] [] s2 s')

/-- With check-quorum off, the quorum check leaves the state. -/
theorem TickCqEnd.of_cq {c : CfgM} {id : w64} {s s1 : NState} (hcq : s.cq = false)
    (h : TickCqEnd c id s s1) : s1 = s := by
  rcases h with h | ⟨h, -⟩
  · exact h
  · rw [hcq] at h; cases h

end pure

section untraced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An untraced `Step`'s gates and closing wand, the end state kept** (`stepBundle_none` with the
caller's closing resource `⌜Q s'⌝` for any `Q` that `StepEndOut` implies). -/
theorem stepBundle_end (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (tl : GoInterface) (Q : NState → Prop) (hQ : ∀ s', StepEndOut c id m ents ctx s s' → Q s')
    (htr : s.gh.tr = none) (Htlok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl : IProp GF) ⊢
      stepGates c r id s m ents sn ctx rs (ghostIn γ md c id s (untracedR γ md c id s)) ∗
      stepClose γ md c id m ents ctx s (untracedR γ md c id s) (fun s' => iprop(⌜Q s'⌝)) := by
  iintro #Htl
  ihave ⟨Hgates, -⟩ := stepBundle_none (GF := GF) γ md c r id s m ents sn ctx rs tl htr Htlok $$ Htl
  iframe Hgates
  unfold stepClose untracedR
  iintro %s' %B %recv %_ %Hend %Hack Hout
  ihave Hout := stepOutG_stepOut c m s _ $$ Hout
  ihave HX := stepOut_const (GF := GF) iprop(emp) (ownStepGhost γ md c id s) s'.outbox $$ Hout
  imodintro
  isplitl [HX]
  · ileft; iframe HX; ipureintro; exact CloseAt.of_none htr
  ipureintro
  exact ⟨hQ s' ⟨Hend, fun h => Hack (.inr h)⟩, OutTrStep.of_none htr⟩

/-- `raft.tickElection.untracedTriple` with the campaign's end state (`TickElEnd`) in the post. -/
abbrev raft.tickElection.untracedEndTriple : Prop :=
  ∀ (c : CfgM) (md : GMode) (γ : RaftNames) (r : Loc) (id : w64) (s : NState),
  uint.Z s.term + 1 < 2 ^ 64 →
  (s.prevote = true → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) →
  NStateWf s →
  uint.Z s.logst.fl ≤ uint.Z s.logst.applied →
  md.Guard s →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickElection")) (Val #()))
  {{ (s' : NState), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md c id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      "%Hcm" ∷ ⌜TickProgress s s'⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ ∗
      "%Hend" ∷ ⌜TickElEnd c id s s'⌝ }}

/-- `raft.tickElection.spec`'s untraced instance, the campaign's end state kept: the campaign's `Step`
at `untracedR`, its closing resource its end state (`stepBundle_end`). -/
theorem raft.tickElection.untracedEnd (h : raft.tickElection.spec (GF := GF) (hG := hG)) :
    raft.tickElection.untracedEndTriple (GF := GF) (hG := hG) := by
  intro c md γ r id s Hterm Htc Hwf Hfla Hpc htr
  iintro %Φ ⟨#Hinit, Hphys, Hghost⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  ihave ⟨Hgates, Hclose⟩ := stepBundle_end (GF := GF) γ md c r id s (tickMsg MsgHup id) [] none [] [] tl
    (StepEndOut c id (tickMsg MsgHup id) [] [] s) (fun _ h => h) htr Htlok $$ Htl
  iapply h c md γ r id s (untracedR γ md c id s)
    (fun s' => iprop(⌜StepEndOut c id (tickMsg MsgHup id) [] [] s s'⌝)) Hterm Htc Hwf Hfla Hpc
    $$ [Hphys Hghost Hgates Hclose]
  · iframe Hinit Hphys Hghost Hgates Hclose
    iempintro
  inext
  iintro %s' H
  iapply HΦ $$ %s'
  iNamed H
  iframe Hphys Hghost
  icases HG with (⟨%Hs, -⟩ | %Hs)
  · ipureintro; exact ⟨Hwf', Hcm, Htick, .inl Hs⟩
  · ipureintro; exact ⟨Hwf', Hcm, Htick, .inr Hs⟩

/-- `raft.tickHeartbeat.untracedTriple` with its `Step`s' end states (`TickHbEnd`) in the post. -/
abbrev raft.tickHeartbeat.untracedEndTriple : Prop :=
  ∀ (c : CfgM) (md : GMode) (γ : RaftNames) (r : Loc) (id : w64) (s : NState),
  NStateWf s →
  md.Guard s →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickHeartbeat")) (Val #()))
  {{ (s' : NState), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md c id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      "%Hcm" ∷ ⌜TickProgress s s'⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ ∗
      "%Hend" ∷ ⌜TickHbEnd c id s s'⌝ }}

/-- `raft.tickHeartbeat.spec`'s untraced instance, the end states kept: each `Step` at `untracedR` of
its state, its closing resource its end state (`stepBundle_end`): the quorum check's
(`TickCqEnd`) and the heartbeat's, from the state the first part left. -/
theorem raft.tickHeartbeat.untracedEnd (h : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    raft.tickHeartbeat.untracedEndTriple (GF := GF) (hG := hG) := by
  intro c md γ r id s Hwf Hpc htr
  iintro %Φ ⟨#Hinit, Hphys, Hghost⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c md γ r id s (untracedR γ md c id s) (fun s1 => iprop(⌜TickCqEnd c id s s1⌝))
    (fun s' => iprop(⌜∃ s1 s2, TickCqEnd c id s s1 ∧ s2.gh = s.gh ∧ s2.role = .leader ∧
      (s2 = s1 ∨ s2 = { s1 with lt := W64 0 }) ∧ StepEndOut c id (tickMsg MsgBeat id) [] [] s2 s'⌝))
    Hwf Hpc $$ [Hphys Hghost]
  · iframe Hinit Hphys Hghost
    isplitr
    · iempintro
    isplitr
    · iintro %hcq
      iapply stepBundle_end (GF := GF) γ md c r id s (tickMsg MsgCheckQuorum id) [] none [] [] tl
        (TickCqEnd c id s) (fun _ h => .inr ⟨hcq, h⟩) htr Htlok
      iexact Htl
    isplitr
    · iintro -; imodintro; ipureintro; exact .inl rfl
    iintro %s1 %s2 %Hs2 %Hg1
    imodintro
    iexists untracedR γ md c id s2
    isplitr
    · iempintro
    iapply stepBundle_end (GF := GF) γ md c r id s2 (tickMsg MsgBeat id) [] none [] [] tl
      (fun s' => ∃ s1 s2, TickCqEnd c id s s1 ∧ s2.gh = s.gh ∧ s2.role = .leader ∧
        (s2 = s1 ∨ s2 = { s1 with lt := W64 0 }) ∧ StepEndOut c id (tickMsg MsgBeat id) [] [] s2 s')
      (fun _ h => ⟨s1, s2, Hg1, Hs2.1, Hs2.2.1, Hs2.2.2, h⟩) (by rw [Hs2.1]; exact htr) Htlok
    iexact Htl
  inext
  iintro %s' H
  iapply HΦ $$ %s'
  iNamed H
  iframe Hphys Hghost
  icases HG with (⟨%s1, %Hs1, %Hg1⟩ | %Hb)
  · ipureintro; exact ⟨Hwf', Hcm, Htick, .inl ⟨s1, Hg1, Hs1⟩⟩
  · ipureintro; exact ⟨Hwf', Hcm, Htick, .inr Hb⟩

end untraced

end EtcdGrove
end Perennial
