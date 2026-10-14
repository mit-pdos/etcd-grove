/-
The ghost state `raft.Step` keeps, in either mode (2026-10-14, reconfiguration stage B7).

* `GMode`: the static mode (the ghost state of B4, at a configuration with the ghost state's
  voters, `CfgStatic`) or the dynamic one (B5's `ownRaftGhostR` over `rOf s g`: a decoder `dec`,
  an initial configuration `c0` with `CfgOk`, and the node's ghost part `g` over the struct's
  configuration).
* `ownStepGhost γ md c id s`: `ownRaftGhost` of `toPState s` in the mode's flag, and what else
  the mode keeps (`ghostRest`). In the dynamic mode it is `ownRaftGhostR` (`ownStepGhost_dyn`).
* `GMode.Pre md m ents s`: the dynamic mode's premises of a step the code cannot check
  (`DynHyp`, `StepLemmasR.lean`): no pre-candidate, A1 at a `MsgStorageApplyResp` (no conf
  entry between the configuration index and the acknowledged index), the log short enough for
  a dropped proposal. (Until 2026-10-14, stage B8, also no `MsgSnap`.)
* `GMode.SnapOk γ md sv scfg` (2026-10-14, stage B8): what a `MsgSnap`'s snapshot must be in the
  mode, beyond `SnapScope`: statically, a non-joint `ConfState` with the ghost state's voters;
  dynamically A3 (`SnapConfOk`, `SnapConf.lean`) of the snapshot's prefix -- any prefix with
  records ending at the snapshot's entry id, which the message itself shows to exist
  (`isMessage_snap_prefix`).
* `GMode.StepOut md c id s s' md'`: the step in the mode's model (`StepC c` statically, `StepR`
  at the fold's configurations dynamically, the ghost part possibly moved: the configuration
  index by `advance`, all of it by a snapshot's restore).
* `ghost_stepCD`: a branch's `StepCD` witness updates the mode's ghost state; `ghost_stepCDS`
  (B8): a `MsgSnap` branch's `StepCDS` witness does.
-/
module

public import Proof.go_etcd_io.raft.v3.StepLemmasR
public import Proof.go_etcd_io.raft.v3.Protocol.RefinementDyn
public import Proof.go_etcd_io.raft.v3.SnapConf
public import Spec.go_etcd_io.raft.v3.raft__restore

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
    s.role ≠ .preCandidate ∧
    (m.Type' = MsgStorageApplyResp →
      s.logst.snap = none ∧
      ∀ e, ents.getLast? = some e → NoConfIn (rOf s g).full g.cidx (uint.nat e.Index')) ∧
    (m.Type' = MsgProp → plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64)

/-- The step in the mode's model: `StepC c` statically, `StepR` at the dynamic configurations
(`AdmFold`: since 2026-10-14, stage B8, a snapshot's restore included; until then no snapshot
prefix, `AdmS dec c0 (fun _ => False)`) dynamically, the ghost part possibly moved (the
configuration index by `StepR.advance`; all of it by `StepR.snapRestore`). -/
def GMode.StepOut (md : GMode) (c : CfgM) (id : w64) (s s' : NState) (md' : GMode) : Prop :=
  match md with
  | .static => md' = .static ∧ ∃ recv, StepC c id (toPState s) recv (toPState s')
  | .dyn dec c0 h0 g => ∃ g', md' = .dyn dec c0 h0 g' ∧
      ∃ recv, StepR (AdmFold dec c0) dec id (rOf s g) recv (rOf s' g')

/-- `GMode.Pre` gives `DynHyp` at any end state whose `applied` moved at most to the
acknowledged index, given the invariant (`applied ≤` the configuration index). -/
theorem GMode.Pre.dynHyp {md : GMode} {m : raftpb.Message} {ents : List raftpb.Entry}
    {s s' : NState} (h : md.Pre m ents s) (Hns : m.Type' ≠ MsgSnap)
    (Hap : m.Type' = MsgStorageApplyResp →
      s'.logst.applied = s.logst.applied ∨
      ∃ e, ents.getLast? = some e ∧ s'.logst.applied = w64Max e.Index' s.logst.applied)
    {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0} {g : RGh} (hmd : md = .dyn dec c0 h0 g)
    (HI : RInv dec c0 (rOf s g)) : DynHyp m s s' g := by
  subst hmd
  obtain ⟨h2, h3, h4⟩ := h
  refine ⟨Hns, h2, HI.full, fun hty => ⟨(h3 hty).1, ?_⟩, h4⟩
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
    · ipureintro
      exact ⟨_, rfl, recv, StepR.mono (fun _ _ h => h.1) HR⟩
    iframe Hfr'
    isplitr
    · ipureintro; exact ⟨HD, hc, HI'⟩
    iintro %hcand; iapply Hc'; exact hcand

/-- What a `MsgSnap`'s snapshot must be in the mode, beyond `SnapScope` (2026-10-14,
reconfiguration stage B8; see the file header): statically, a non-joint `ConfState` with the
ghost state's voters (the configuration a restore installs is then still `CfgStatic`);
dynamically, A3 -- the `ConfState` denotes the fold of the snapshot's prefix (`SnapConfOk`), for
any recorded prefix ending at the snapshot's entry id (records agree, so there is one; the
message shows one exists, `isMessage_snap_prefix`). -/
def GMode.SnapOk (γ : RaftNames) : GMode → raftpb.Snapshot → CSLists → IProp GF
  | .static, _, scfg => iprop(⌜GMap.listToSet scfg.voters = γ.reCfg ∧ scfg.outgoing = []⌝)
  | .dyn dec c0 _ _, sv, scfg => iprop(□ ∀ (fp : List raftpb.Entry), logRecs γ base0 fp -∗
      ⌜FullOk (snapId sv) fp⌝ -∗
      ⌜SnapConfOk dec c0 fp scfg.outgoing scfg.voters scfg.learners scfg.learnersNext
        sv.Metadata'.ConfState'.AutoLeave'⌝)

instance GMode.SnapOk_persistent (γ : RaftNames) (md : GMode) (sv : raftpb.Snapshot)
    (scfg : CSLists) : Persistent (md.SnapOk (GF := GF) γ sv scfg) := by
  cases md <;> unfold GMode.SnapOk <;> infer_instance

/-- An id `restore`'s `found` search finds is an id of the configuration the `ConfState`
denotes. -/
theorem snapCfg_ids {sv : raftpb.Snapshot} {scfg : CSLists} {id : w64} (h : scfg.Has id) :
    id ∈ (snapCfg sv scfg).ids := by
  unfold snapCfg csCfgM CfgM.ids CfgM.voters
  rcases h with h | h | h
  · exact GMap.elem_of_union_l _ (GMap.elem_of_union_l _ ((GMap.elem_of_list_to_set _ _).2 h))
  · exact GMap.elem_of_union_r _ ((GMap.elem_of_list_to_set _ _).2 h)
  · exact GMap.elem_of_union_l _ (GMap.elem_of_union_r _ ((GMap.elem_of_list_to_set _ _).2 h))

/-- A `MsgSnap` branch's step updates the mode's ghost state (2026-10-14, stage B8): statically
`ownRaftGhost_stepC`, the configuration afterwards still the ghost state's (`GMode.SnapOk`);
dynamically `ownRaftGhostR_stepR` at the snapshot's prefix `fp0`, the one the message shows
(`isMessage_snap_prefix`), whose fold the `ConfState` denotes (`GMode.SnapOk`). -/
theorem ghost_stepCDS (γ : RaftNames) (md : GMode) (c c' : CfgM) (id : w64)
    (sv : raftpb.Snapshot) (scfg : CSLists) (s : NState) (recv : List Msg) (s' : NState)
    (a : Msg) (Ha : a.ty = .snap ∧ entryID.mk a.logterm a.index = snapId sv)
    (Hstep : StepCDS c c' (snapCfg sv scfg) id (snapId sv) s recv s')
    (Hid : scfg.Has id) (Hc' : c' = c ∨ c' = snapCfg sv scfg) :
    ⊢ isMessage (GF := GF) γ a -∗ ([∗list] x ∈ recv, isMessage γ x) -∗ rdCred γ (rdCount recv) -∗
      md.SnapOk γ sv scfg -∗ ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id s s' md'⌝ ∗
        ownRaftGhost γ id (toPState s') md'.isDyn ∗ ghostRest γ md' c' id s' := by
  cases md with
  | static =>
    simp only [ghostRest, GMode.isDyn, GMode.SnapOk]
    iintro - Hrecv Hcr %Hso Hg %HC
    imod ownRaftGhost_stepC γ c HC id (toPState s) recv (toPState s') Hstep.1 $$ Hrecv Hcr Hg
      with Hg
    imodintro
    iexists GMode.static
    iframe Hg
    isplitr
    · ipureintro; exact ⟨rfl, recv, Hstep.1⟩
    ipureintro
    rcases Hc' with rfl | rfl
    · exact HC
    · refine ⟨?_, ?_, HC.2.2⟩
      · simp only [snapCfg, csCfgM]; exact Hso.1
      · simp only [snapCfg, csCfgM]; rw [Hso.2]; try rfl
  | dyn dec c0 h0 g =>
    simp only [ghostRest, GMode.isDyn, GMode.SnapOk]
    iintro #Hm Hrecv Hcr #Hso Hg ⟨%Hdc, #Hfr, #Hc⟩
    obtain ⟨HD, hc, HI⟩ := Hdc
    -- the snapshot's prefix, from the message, and A3 of it
    icases isMessage_snap_prefix γ a Ha.1 $$ Hm with ⟨%fp0, %Hfp0, #Hr0⟩
    rw [Ha.2] at Hfp0
    ihave %Hsc := Hso $$ %fp0 Hr0 %Hfp0
    obtain ⟨-, cs, Hfold, Hcs⟩ := Hsc
    obtain ⟨g', hg', HR⟩ := Hstep.2 (AdmS dec c0 (fun fp => fp = fp0)) dec g fp0 cs hc Hfp0
      Hcs.symm (snapCfg_ids Hid) ⟨Hfold, rfl⟩
    ihave Hown : ownRaftGhostR γ dec c0 id (rOf s g) $$ [Hg]
    · simp only [ownRaftGhostR, rOf.proj_p, rOf.proj_fp]
      iframe Hg Hfr
      isplitr
      · ipureintro; exact HI
      iintro %hcand; iapply Hc; exact hcand
    imod ownRaftGhostR_stepR γ dec c0 h0 HD (fun fp => fp = fp0) id (rOf s g) recv _ HR
      $$ [] Hrecv Hcr Hown with Hown
    · imodintro
      iintro %fp %h
      subst h
      iexact Hr0
    imodintro
    iexists GMode.dyn dec c0 h0 g'
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI', #Hfr', #Hc'⟩
    simp only [GMode.isDyn, rOf.proj_p, rOf.proj_fp]
    iframe Hg
    isplitr
    · ipureintro
      exact ⟨g', rfl, recv, StepR.mono (fun _ _ h => h.1) HR⟩
    iframe Hfr'
    isplitr
    · ipureintro; exact ⟨HD, hg', HI'⟩
    iintro %hcand; iapply Hc'; exact hcand

end ghost

end EtcdGrove
end Perennial
