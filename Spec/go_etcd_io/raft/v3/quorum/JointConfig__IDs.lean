/-
Port of `election_proof/spec_JointConfig__IDs.v` (feb5c73d4).

Lean notes: the type of Rocq's untyped binder `tv` is written out
(`tracker.ProgressTracker`); Rocq's `trk.t` record is `Trk`.
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

/-- The ids of the voters, in some order, as `campaign` enumerates them: a fresh map
with the keys of the incoming voter map `v` (the outgoing one being `nil`, the
non-joint case). `campaign` calls this on `&r.trk.Config.Voters`, so the receiver is a
field ref and not the tracker itself; `IDs.spec_tracker` below is that form.

**In scope. The translation defect that blocked this is fixed** (2026-09-17); what is
left is ordinary proof work.

Until 2026-09-17 Goose emitted the element read `c[0]` inside `JointConfig.IDs` as
`![MajorityConfig] (IndexRef (ArrayType 2 MajorityConfig) (c, 0))`, which Perennial's
`load`/`index_ref` lemmas could not step (they expect the array element access to go
through `arrayIndexRef`). `etc/update-goose-new.py` now emits `IndexRef JointConfig`,
which steps (`index_ref_array'`), so the proof goes through.

Generalized 2026-10-08 (when `confchange` was translated): stated on any `JointConfig`
cell at any fraction, with the voter map at any fraction, since `checkInvariants` calls
it on a local copy of a `Config`; the tracker form it used to state is derived.

Generalized again 2026-10-12, for joint configurations: either half of the `JointConfig`
may be `nil` or a map (`ownIdsetQ`), and the result is the union of the two sets. -/
abbrev quorum.JointConfig.IDs.spec : Prop :=
  ∀ (p : Loc) (jc : quorum.JointConfig) (v0 v1 : Loc) (s0 s1 : GMap w64 Unit)
    (dq dq0 dq1 : DFrac),
  jc.arr = [v0, v1] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗
      p ↦{dq} jc ∗ ownIdsetQ v0 dq0 s0 ∗ ownIdsetQ v1 dq1 s1 }}
    (App (Val (p @!! go.GoType.PointerType quorum.JointConfig.ty @!! go!"IDs")) (Val #()))
  {{ (mref : Loc), RET #mref;
      p ↦{dq} jc ∗ ownIdsetQ v0 dq0 s0 ∗ ownIdsetQ v1 dq1 s1 ∗ mref ↦$ (s0 ∪ s1) }}

/-- The tracker form: `IDs` on `&trk.Config.Voters` with the tracker sealed, as
`campaign` and `VoterNodes` call it (the statement this spec had until 2026-10-08). -/
theorem quorum.JointConfig.IDs.spec_tracker
    (H : quorum.JointConfig.IDs.spec (GF := GF) (hG := hG))
    (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ trk ↦ tv ∗
        ownTracker cfg tv t }}
      (App (Val (((trk.[tracker.ProgressTracker, go!"Config"]).[tracker.Config, go!"Voters"])
        @!! go.GoType.PointerType quorum.JointConfig.ty @!! go!"IDs")) (Val #()))
    {{ (mref : Loc) (idm : GMap w64 Unit), RET #mref;
        trk ↦ tv ∗ ownTracker cfg tv t ∗
        mref ↦$ idm ∗ ⌜domSet idm = cfg⌝ }} := by
  obtain ⟨votes, prs, pvs⟩ := t
  iintro %Φ ⟨#Hpkg, Htrk, Hown⟩ HΦ
  iNamed Hown
  -- the field `trk.Config.Voters` out of the struct, and back after the call
  icases (Access.access (A := iprop(
      (trk.[tracker.ProgressTracker, go!"Config"]).[tracker.Config, go!"Voters"] ↦
        tv.Config'.Voters'))
    (A' := iprop((trk.[tracker.ProgressTracker, go!"Config"]).[tracker.Config, go!"Voters"] ↦
        tv.Config'.Voters'))
    (P := iprop(trk ↦ tv))) $$ Htrk with ⟨Hf, Hback⟩
  ihave %Hvnn := ownMap_not_nil _ _ _ $$ Hvoters
  iapply H _ _ _ _ voters ∅ _ (DFrac.own 1) (DFrac.own 1) Hvoters_arr $$ [$Hf Hvoters]
  · iPkgInit
    isplitl [Hvoters]
    · unfold ownIdsetQ; iright; iexact Hvoters
    · unfold ownIdsetQ; ileft; ipureintro; exact ⟨rfl, rfl⟩
  inext
  iintro %mref ⟨Hf, Hvoters, -, Hidm⟩
  unfold ownIdsetQ
  icases Hvoters with (%Hc | Hvoters)
  · exact absurd Hc.1 Hvnn
  iapply HΦ
  ihave Htrk := Hback $$ Hf
  iframe Htrk Hidm
  isplitl [Hvotes Hprogs Hvoters Hlearners HlearnersNext]
  · iapply ownTracker_intro cfg tv votes prs pvs voters_ref voters learners learnersNext
      Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
      $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext
  ipureintro
  rw [GMap.map_union_empty, Hvoters_dom]

end spec

end EtcdGrove
end Perennial
