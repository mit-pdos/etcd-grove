/-
`(*ProgressTracker).ResetReplicationSet` (raft#168, `tracker/tracker.go`; 2026-10-19, witness
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

/-- `p.ResetReplicationSet(b)`: a fresh epoch, installed (`p.Epoch`), read-only from then on, of
subterm `0` (`b`, a new term) or the old one plus one (a configuration change), whose replication
sets are the configuration's with each half's witness excluded (`resetEpoch`): the bare epoch
when the configuration has no witness. Stated on the fields it reads: the voter halves (any
fraction, a nil half empty), the witnesses, and with `b = false` the old epoch's subterm. -/
abbrev tracker.ProgressTracker.ResetReplicationSet.spec : Prop :=
  ∀ (trk : Loc) (tv : tracker.ProgressTracker) (b : Bool) (vin vout : Loc) (dqv : DFrac)
    (V0 V1 : GSet w64) (w0 w1 sub : w64),
  tv.Config'.Voters'.arr = [vin, vout] → tv.Config'.Witnesses'.arr = [w0, w1] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownIdsetQ vin dqv V0 ∗ ownIdsetQ vout dqv V1 ∗
      (⌜b = true⌝ ∨ tv.Epoch'.[tracker.Epoch, go!"Subterm"] ↦□ sub) }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
      @!! go!"ResetReplicationSet")) (Val #b))
  {{ (e : Loc), RET #();
      trk ↦ { tv with Epoch' := e } ∗ ownIdsetQ vin dqv V0 ∗ ownIdsetQ vout dqv V1 ∗
      ownEpoch e (resetEpoch V0 V1 w0 w1 (if b then W64 0 else sub + W64 1)) }}

/-- With `true` at a witness-free tracker (the statement this spec had until the epoch model):
the tracker the same but for its epoch, witness-free again. -/
theorem tracker.ProgressTracker.ResetReplicationSet.spec_nw
    (H : tracker.ProgressTracker.ResetReplicationSet.spec (GF := GF) (hG := hG))
    (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
        ownTrackerC c tv t }}
      (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
        @!! go!"ResetReplicationSet")) (Val #true))
    {{ (e : Loc), RET #();
        trk ↦ { tv with Epoch' := e } ∗ ownTrackerC c { tv with Epoch' := e } t }} := by
  iintro %Φ ⟨#Hpkg, Htrk, Hown⟩ HΦ
  iunfold ownTrackerC at Hown
  iNamed Hown
  icases ownCfgCC_elim _ _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal, %Hwit⟩
  ihave %Hvnn := ownMap_not_nil _ _ _ $$ Hin
  -- the outgoing half's canonical form, kept across the call
  ihave %Hpo : ⌜(vout = map.nil ∧ c.outgoing = ∅) ∨ c.outgoing ≠ ∅⌝ $$ [Hout]
  · unfold ownIdsetC
    icases Hout with (%H | ⟨-, %H⟩)
    · ipureintro; exact Or.inl H
    · ipureintro; exact Or.inr H
  have HspecE := H trk tv true vin vout (DFrac.own 1) c.incoming c.outgoing (W64 0) (W64 0) (W64 0)
    Harr Hwit
  rw [resetEpoch_nw] at HspecE
  simp only [↓reduceIte] at HspecE
  iapply HspecE $$ [Htrk Hin Hout]
  · iframe Hpkg Htrk
    isplitl [Hin]
    · unfold ownIdsetQ; iright; iexact Hin
    isplitl [Hout]
    · iapply ownIdsetC_Q $$ Hout
    ileft; ipureintro; trivial
  inext
  iintro %e ⟨Htrk, Hin, Hout, #He⟩
  iapply HΦ
  iframe Htrk
  unfold ownIdsetQ
  icases Hin with (%Hnil | Hin)
  · exact absurd Hnil.1 Hvnn
  ihave Hout : ownIdsetC vout (DFrac.own 1) c.outgoing $$ [Hout]
  · unfold ownIdsetC
    icases Hout with (%Hn | Ho)
    · ileft; ipureintro; exact Hn
    · ihave %Honn := ownMap_not_nil _ _ _ $$ Ho
      iright; iframe Ho
      ipureintro
      rcases Hpo with Hp | Hp
      · exact absurd Hp.1 Honn
      · exact Hp
  iapply ownTrackerC_intro c { tv with Epoch' := e } t.votes t.prs t.peers Hinv Hdom Hflags
    Hsize HmaxInfl Hnw $$ Hvotes Hprs Hprogs [Hin Hout Hl Hln] [He]
  · iapply ownCfgCC_intro _ _ c vin vout Harr Hal Hwit $$ Hin Hout Hl Hln
  · iunfold ownEpochNW; iexact He

end spec

end EtcdGrove
end Perennial
