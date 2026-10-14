/-
The ghost state `raft.Step` keeps, in either mode (2026-10-14, reconfiguration stage B7).

* `GMode`: the static mode (the ghost state of B4, at a configuration with the ghost state's
  voters, `CfgStatic`) or the dynamic one (B5's `ownRaftGhostR` over `rOf s g`: a decoder `dec`,
  an initial configuration `c0` with `CfgOk`, and the node's ghost part `g` over the struct's
  configuration).
* `ownStepGhost γ md c id s`: `ownRaftGhost` of `toPState s` in the mode's flag, and what else
  the mode keeps (`ghostRest`). In the dynamic mode it is `ownRaftGhostR` (`ownStepGhost_dyn`).
* `GMode.Pre md m ents s`: the dynamic mode's premises of a step the code cannot check
  (`DynHyp`, `StepLemmasR.lean`): no `MsgSnap` (B8), no pre-candidate, A1 at a
  `MsgStorageApplyResp` (no conf entry between the configuration index and the acknowledged
  index), the log short enough for a dropped proposal.
* `GMode.StepOut md c id s s' md'`: the step in the mode's model (`StepC c` statically, `StepR`
  dynamically, the configuration index possibly moved).
* `ghost_stepCD`: a branch's `StepCD` witness updates the mode's ghost state.
-/
module

public import Proof.go_etcd_io.raft.v3.StepLemmasR
public import Proof.go_etcd_io.raft.v3.Protocol.RefinementDyn

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode GMap go_etcd_io.raft.v3

section mode
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The mode of the ghost state `raft.Step` keeps (see the file header). -/
inductive GMode where
  | static
  | dyn (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh)

/-- The flag `ownRaftGhost` carries. -/
def GMode.isDyn : GMode → Bool
  | .static => false
  | .dyn .. => true

/-- The dynamic mode's premises of a step of `raft.Step` the code cannot check (see the file
header); none in the static mode. -/
def GMode.Pre (md : GMode) (m : raftpb.Message) (ents : List raftpb.Entry) (s : NState) : Prop :=
  match md with
  | .static => True
  | .dyn _ _ _ g =>
    m.Type' ≠ MsgSnap ∧ s.role ≠ .preCandidate ∧
    (m.Type' = MsgStorageApplyResp →
      s.logst.snap = none ∧
      ∀ e, ents.getLast? = some e → NoConfIn (rOf s g).full g.cidx (uint.nat e.Index')) ∧
    (m.Type' = MsgProp → plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64)

/-- The step in the mode's model: `StepC c` statically, `StepR` at the dynamic configurations
(no snapshot prefix: a snapshot restore is outside the dynamic scope) dynamically, the
configuration index possibly moved (`StepR.advance`). -/
def GMode.StepOut (md : GMode) (c : CfgM) (id : w64) (s s' : NState) (md' : GMode) : Prop :=
  match md with
  | .static => md' = .static ∧ ∃ recv, StepC c id (toPState s) recv (toPState s')
  | .dyn dec c0 h0 g => ∃ cidx', md' = .dyn dec c0 h0 { g with cidx := cidx' } ∧
      ∃ recv, StepR (AdmS dec c0 (fun _ => False)) dec id (rOf s g) recv
        (rOf s' { g with cidx := cidx' })

/-- `GMode.Pre` gives `DynHyp` at any end state whose `applied` moved at most to the
acknowledged index, given the invariant (`applied ≤` the configuration index). -/
theorem GMode.Pre.dynHyp {md : GMode} {m : raftpb.Message} {ents : List raftpb.Entry}
    {s s' : NState} (h : md.Pre m ents s)
    (Hap : m.Type' = MsgStorageApplyResp →
      s'.logst.applied = s.logst.applied ∨
      ∃ e, ents.getLast? = some e ∧ s'.logst.applied = w64Max e.Index' s.logst.applied)
    {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0} {g : RGh} (hmd : md = .dyn dec c0 h0 g)
    (HI : RInv dec c0 (rOf s g)) : DynHyp m s s' g := by
  subst hmd
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, HI.full, fun hty => ⟨(h3 hty).1, ?_⟩, h4⟩
  have Hac : uint.nat s.logst.applied ≤ g.cidx := HI.applied_cidx
  have Hempty : ∀ n, n ≤ g.cidx → NoConfIn (rOf s g).full g.cidx n :=
    fun n hn k e hk1 hk2 => absurd (Nat.lt_of_lt_of_le hk2 hn) (Nat.not_lt.2 hk1)
  rcases Hap hty with ha | ⟨e, he, ha⟩
  · rw [ha]; exact Hempty _ Hac
  · rw [ha]
    unfold w64Max
    split
    · exact (h3 hty).2 e he
    · exact Hempty _ Hac

end mode

section ghost
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- What the mode keeps beyond `ownRaftGhost`: statically, the configuration's voters are the
ghost state's; dynamically, `ownRaftGhostR`'s invariant, full prefix records and campaign
record, with the ghost part over the configuration. -/
def ghostRest (γ : RaftNames) : GMode → CfgM → w64 → NState → IProp GF
  | .static, c, _, _ => iprop(⌜CfgStatic γ c⌝)
  | .dyn dec c0 h0 g, c, id, s =>
    iprop(⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ g.cfg.cfg = c ∧ RInv dec c0 (rOf s g)⌝ ∗
      logRecs γ base0 g.fp ∗
      (∀ (_ : (toPState s).role = .candidate),
        isCampK γ id (toPState s).term (rOf s g).full (toPState s).commit))

/-- The ghost state `raft.Step` keeps (see the file header). -/
def ownStepGhost (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) : IProp GF :=
  iprop(ownRaftGhost γ id (toPState s) md.isDyn ∗ ghostRest γ md c id s)

/-- In the dynamic mode, `ownStepGhost` is `ownRaftGhostR`. -/
theorem ownStepGhost_dyn (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh)
    (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ (.dyn dec c0 h0 g) c id s ⊣⊢
      ⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ g.cfg.cfg = c⌝ ∗
        ownRaftGhostR γ dec c0 id (rOf s g) := by
  simp only [ownStepGhost, ghostRest, GMode.isDyn, ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
  constructor
  · iintro ⟨Hg, %Hdc, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    isplitr
    · ipureintro; exact ⟨HD, hc⟩
    iframe Hg Hfr
    isplitr
    · ipureintro; exact HI
    iintro %hcand; iapply Hc; exact hcand
  · iintro ⟨%Hdc, Hg, %HI, #Hfr, #Hc⟩
    obtain ⟨HD, hc⟩ := Hdc
    iframe Hg Hfr
    isplitr
    · ipureintro; exact ⟨HD, hc, HI⟩
    iintro %hcand; iapply Hc; exact hcand

/-- A branch's step updates the mode's ghost state: statically `ownRaftGhost_stepC`,
dynamically `ownRaftGhostR_stepR` (the premises `DynHyp` from `Hdh`, given the invariant). -/
theorem ghost_stepCD (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : raftpb.Message)
    (s : NState) (recv : List Msg) (s' : NState) (Hstep : StepCD c id m s recv s')
    (Hdh : ∀ (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh), md = .dyn dec c0 h0 g →
      RInv dec c0 (rOf s g) → DynHyp m s s' g) :
    ⊢ ([∗list] x ∈ recv, isMessage (GF := GF) γ x) -∗ rdCred γ (rdCount recv) -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRest γ md' c id s' := by
  cases md with
  | static =>
    simp only [ghostRest, GMode.isDyn]
    iintro Hrecv Hcr Hg %HC
    imod ownRaftGhost_stepC γ c HC id (toPState s) recv (toPState s') Hstep.1 $$ Hrecv Hcr Hg
      with Hg
    imodintro
    iexists GMode.static
    iframe Hg
    isplitr
    · ipureintro; exact ⟨rfl, recv, Hstep.1⟩
    ipureintro; exact HC
  | dyn dec c0 h0 g =>
    simp only [ghostRest, GMode.isDyn]
    iintro Hrecv Hcr Hg ⟨%Hdc, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    obtain ⟨cidx', HR⟩ := Hstep.2 (AdmS dec c0 (fun _ => False)) dec g hc
      (Hdh dec c0 h0 g rfl HI)
    ihave Hown : ownRaftGhostR γ dec c0 id (rOf s g) $$ [Hg]
    · simp only [ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
      iframe Hg Hfr
      isplitr
      · ipureintro; exact HI
      iintro %hcand; iapply Hc; exact hcand
    imod ownRaftGhostR_stepR γ dec c0 h0 HD (fun _ => False) id (rOf s g) recv _ HR
      $$ [] Hrecv Hcr Hown with Hown
    · imodintro
      iintro %fp %h
      exact h.elim
    imodintro
    iexists GMode.dyn dec c0 h0 { g with cidx := cidx' }
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI', #Hfr', #Hc'⟩
    simp only [GMode.isDyn, rOf.proj_p, rOf.proj_fp]
    iframe Hg
    isplitr
    · ipureintro; exact ⟨cidx', rfl, recv, HR⟩
    iframe Hfr'
    isplitr
    · ipureintro; exact ⟨HD, hc, HI'⟩
    iintro %hcand; iapply Hc'; exact hcand

end ghost

end EtcdGrove
end Perennial
