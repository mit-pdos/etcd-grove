/-
`(*ProgressTracker).ChangeReplicationSet` (raft#168, `tracker/tracker.go`; 2026-10-19, witness
support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTrackerC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `ChangeReplicationSet` reads past the epoch when the epoch has a witness: the progress
map (each half's excluded voter's `RecentActive` and `State`, and every peer's `RecentActive`),
whose peers include the halves' voters (`V0`, `V1`, of which the epoch is: `EpochWF`), none of
them `0`; and the tracker whole, to install the new epoch. -/
def chgRes (dq : DFrac) (tv : tracker.ProgressTracker) (V0 V1 : GSet w64) (w0 w1 : w64)
    (em : EpochM) (pvs : GMap w64 Progress) : IProp GF :=
  iprop(⌜dq = DFrac.own 1 ∧ EpochWF V0 V1 w0 w1 em ∧ W64 0 ∉ V0 ∧ W64 0 ∉ V1 ∧
      ∀ v, v ∈ V0 ∨ v ∈ V1 → (pvs !! v).isSome⌝ ∗
    ownProgressMap tv.Progress' pvs)

/-- `p.ChangeReplicationSet()`: `false`, nothing changed, with a witness-free epoch (the early
return, which reads nothing but the epoch); else, given what it reads (`chgRes`), `false` with
nothing changed, or `true` with a new epoch installed (`p.Epoch`), read-only, the next subterm's,
with the same witnesses and both halves well formed (`ChangeEpochOk`: which voter it excludes
depends on `RecentActive`, which the `Progress` model leaves out). -/
abbrev tracker.ProgressTracker.ChangeReplicationSet.spec : Prop :=
  ∀ (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker) (em : EpochM) (V0 V1 : GSet w64)
    (w0 w1 : w64) (pvs : GMap w64 Progress),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
      ownEpoch tv.Epoch' em ∗
      (⌜em.hasWit = false⌝ ∨ chgRes dq tv V0 V1 w0 w1 em pvs) }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
      @!! go!"ChangeReplicationSet")) (Val #()))
  {{ (ch : Bool) (e : Loc), RET #ch; trk ↦{dq} { tv with Epoch' := e } ∗
      (⌜em.hasWit = false⌝ ∨ chgRes dq tv V0 V1 w0 w1 em pvs) ∗
      (⌜ch = false ∧ e = tv.Epoch'⌝ ∨
       ⌜ch = true ∧ em.hasWit = true⌝ ∗ ∃ em', ownEpoch e em' ∗
         ⌜ChangeEpochOk V0 V1 w0 w1 em em'⌝) }}

/-- With a witness-free epoch, `false` (the statement this spec had until the epoch model):
`stepLeader`'s check-quorum then starts no subterm. -/
theorem tracker.ProgressTracker.ChangeReplicationSet.spec_nw
    (H : tracker.ProgressTracker.ChangeReplicationSet.spec (GF := GF) (hG := hG))
    (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
        ownEpochNW tv.Epoch' }}
      (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
        @!! go!"ChangeReplicationSet")) (Val #()))
    {{ RET #false; trk ↦{dq} tv }} := by
  iintro %Φ ⟨#Hpkg, Htrk, #He⟩ HΦ
  iunfold ownEpochNW at He
  iapply H trk dq tv (EpochM.bare (W64 0)) ∅ ∅ (W64 0) (W64 0) ∅ $$ [Htrk]
  · iframe Hpkg Htrk He
    ileft; ipureintro; simp [EpochM.hasWit, EpochM.bare, RSM.bare]
  inext
  iintro %ch %e ⟨Htrk, -, (%Hch | ⟨%Hch, -⟩)⟩
  · obtain ⟨rfl, rfl⟩ := Hch
    iapply HΦ $$ Htrk
  · exfalso
    simp [EpochM.hasWit, EpochM.bare, RSM.bare] at Hch

/-- At a tracker of the configuration `c` (2026-10-20, witness support): `false` with nothing
changed, or `true` with an epoch that had a witness changed to the next subterm's
(`ChangeEpochOk`), the tracker otherwise the same. -/
theorem tracker.ProgressTracker.ChangeReplicationSet.spec_c
    (H : tracker.ProgressTracker.ChangeReplicationSet.spec (GF := GF) (hG := hG))
    (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
        ownTrackerC c tv t }}
      (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
        @!! go!"ChangeReplicationSet")) (Val #()))
    {{ (ch : Bool) (e : Loc), RET #ch; trk ↦ { tv with Epoch' := e } ∗
        if ch then
          ∃ em', ⌜t.ep.hasWit = true ∧ ChangeEpochOk c.incoming c.outgoing c.wit (W64 0) t.ep em'⌝ ∗
            ownTrackerC c { tv with Epoch' := e } { t with ep := em' }
        else ⌜e = tv.Epoch'⌝ ∗ ownTrackerC c tv t }} := by
  iintro %Φ ⟨#Hpkg, Htrk, Hown⟩ HΦ
  icases ownTrackerC_no0 c tv t $$ Hown with ⟨%H0, Hown⟩
  have H0i : W64 0 ∉ c.incoming := fun h => H0 ((GMap.elem_of_subseteq _ _).1 (voters_sub_ids c) _
    ((GMap.elem_of_subseteq _ _).1 (incoming_sub_voters c) _ h))
  have H0o : W64 0 ∉ c.outgoing := fun h => H0 ((GMap.elem_of_subseteq _ _).1 (voters_sub_ids c) _
    ((GMap.elem_of_subseteq _ _).1 (outgoing_sub_voters c) _ h))
  iunfold ownTrackerC at Hown
  iNamed Hown
  iunfold ownEpochOk at Hepoch
  icases Hepoch with ⟨#He, %Hok⟩
  cases hw : t.ep.hasWit with
  | false =>
    iapply H trk (DFrac.own 1) tv t.ep c.incoming c.outgoing c.wit (W64 0) t.peers $$ [Htrk]
    · iframe Hpkg Htrk He; ileft; ipureintro; exact hw
    inext
    iintro %ch %e ⟨Htrk, -, (%Hch | ⟨%Hch, -⟩)⟩
    · obtain ⟨rfl, rfl⟩ := Hch
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Htrk
      isplitr; · ipureintro; rfl
      iapply ownTrackerC_intro c tv t.votes t.prs t.peers Hinv Hdom Hflags Hsize HmaxInfl Hnw
        $$ Hvotes Hprs Hprogs Hcfg [He]
      unfold ownEpochOk; iframe He; ipureintro; exact Hok
    · exfalso; rw [hw] at Hch; cases Hch.2
  | true =>
    obtain ⟨Hwnz, Hwf⟩ := EpochOkC.wf Hok hw
    ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
    iapply H trk (DFrac.own 1) tv t.ep c.incoming c.outgoing c.wit (W64 0) t.peers
      $$ [Htrk Hprogs]
    · iframe Hpkg Htrk He
      iright
      unfold chgRes
      isplitr
      · ipureintro
        refine ⟨rfl, Hwf, H0i, H0o, fun v hv => ?_⟩
        have hv' : v ∈ c.ids := by
          rcases hv with hv | hv
          · exact (GMap.elem_of_subseteq _ _).1 (voters_sub_ids c) _
              ((GMap.elem_of_subseteq _ _).1 (incoming_sub_voters c) _ hv)
          · exact (GMap.elem_of_subseteq _ _).1 (voters_sub_ids c) _
              ((GMap.elem_of_subseteq _ _).1 (outgoing_sub_voters c) _ hv)
        rw [← Hdom, GMap.elem_of_dom', GMap.mem_iff] at hv'
        exact (Hiff v).1 hv'
      unfold ownProgressMap
      iexists t.prs
      iframe Hprs Hprogs
    inext
    iintro %ch %e ⟨Htrk, Hres, Hch⟩
    icases Hres with (%Hf | Hres)
    · rw [hw] at Hf; cases Hf
    unfold chgRes
    icases Hres with ⟨-, HP⟩
    iunfold ownProgressMap at HP
    icases HP with ⟨%prs', #Hprs', Hprogs⟩
    ihave %Hprs_eq := progress_map_agree _ _ _ _ _ $$ Hprs Hprs'
    subst Hprs_eq
    icases Hch with (%Hch | ⟨%Hch, %em', #He', %Hchg⟩)
    · obtain ⟨rfl, rfl⟩ := Hch
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Htrk
      isplitr; · ipureintro; rfl
      iapply ownTrackerC_intro c tv t.votes t.prs t.peers Hinv Hdom Hflags Hsize HmaxInfl Hnw
        $$ Hvotes Hprs Hprogs Hcfg [He]
      unfold ownEpochOk; iframe He; ipureintro; exact Hok
    · obtain ⟨rfl, -⟩ := Hch
      iapply HΦ
      simp only [↓reduceIte]
      iframe Htrk
      iexists em'
      isplitr; · ipureintro; exact ⟨hw, Hchg⟩
      iapply ownTrackerC_intro c { tv with Epoch' := e } t.votes t.prs t.peers Hinv Hdom Hflags
        Hsize HmaxInfl Hnw $$ Hvotes Hprs Hprogs Hcfg [He']
      unfold ownEpochOk; iframe He'; ipureintro; exact EpochOkC.of_wf Hwnz Hchg.2.1

end spec

end EtcdGrove
end Perennial
