/- Port of election_proof/proof_ProgressTracker__ConfState.v. -/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ConfState
public import Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__Slice

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit package_sem in
/-- `array_acc`, putting back the same element. -/
private theorem array_acc_same' {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (i : Int) (dq : DFrac) (n : Int) (a : GoArray V n) (v : V)
    (hpos : 0 ≤ i) (hlookup : a.arr[i.toNat]? = some v) :
    typedPointsto (GF := GF) p a dq ⊢
      iprop(typedPointsto (arrayIndexRef V i p) v dq ∗
        (typedPointsto (arrayIndexRef V i p) v dq -∗ typedPointsto p a dq)) := by
  have hset : a.arr.set i.toNat v = a.arr := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hlookup
    exact List.set_getElem_self h
  iintro Ha
  icases array_acc (GF := GF) p i dq n a v hpos hlookup $$ Ha with ⟨Hv, Ha⟩
  iframe Hv
  iintro Hv
  ihave Ha := Ha $$ %v Hv
  rw [hset]
  iexact Ha

/-- The four `Slice` calls, each on its id set (`ownIdsetOpt`, i.e. `ownIdsetQ` read whole):
the two halves of `p.Voters` through the array field, then `p.Learners` and
`p.LearnersNext`. -/
theorem tracker.ProgressTracker.ConfState.wp_proof
    (wp_MajorityConfig_Slice : quorum.MajorityConfig.Slice.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG) := by
  intro c trk tv t hw
  obtain ⟨votes, prs, pvs, ep⟩ := t
  wp_start as ⟨Htrk, Hown⟩
  iapply wp_fupd
  iunfold ownTrackerC at Hown
  iNamed Hown
  simp only at Hinv Hdom Hflags Hsize
  icases ownCfgCC_elim _ _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal, %Hwit⟩
  have Hsz : ∀ s : GSet w64, s ⊆ c.ids → (GMap.size s : Int) ≤ 2 ^ 62 := by
    intro s hs
    have := size_le_of_sub_dom s prs (by rw [Hdom]; exact hs)
    omega
  wp_auto
  -- `Voters[0].Slice()`: the receiver is a pointer into the tracker's `JointConfig`
  -- array. Split the array field out of `trk ↦ tv` and element 0 out of the array.
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
        tv.Config'.Voters')
      (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
        tv.Config'.Voters')
      (P := trk ↦ tv)) $$ Htrk with ⟨Hvf, Htrkback⟩
  icases array_acc _ (sint.Z (W64 0)) _ _ _ vin (by decide) (by rw [Harr]; rfl)
    $$ Hvf with ⟨Hc0, Hcback⟩
  wp_method_call
  wp_call
  wp_auto
  ihave %Hvin_nn := ownMap_not_nil $$ Hin
  wp_apply wp_MajorityConfig_Slice _ c.incoming $$ [Hin] as %sl0 %xs0 ⟨Hin, Hsl0, -, %Hxs0⟩
  · isplitl
    · unfold ownIdsetOpt; iright; iexact Hin
    · ipureintro; exact Hsz _ (incoming_sub_ids c)
  ihave Hvf := Hcback $$ Hc0
  -- element 1, the outgoing voters
  icases array_acc _ (sint.Z (W64 1)) _ _ _ vout (by decide) (by rw [Harr]; rfl)
    $$ Hvf with ⟨Hc1, Hcback⟩
  wp_method_call
  wp_call
  wp_auto
  icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hoq, %Hoc⟩
  wp_apply wp_MajorityConfig_Slice vout c.outgoing $$ [Hoq] as %sl1 %xs1 ⟨Hoo, Hsl1, -, %Hxs1⟩
  · isplitl
    · unfold ownIdsetOpt; iapply ownIdsetQ_elim _ _ _ $$ Hoq
    · ipureintro; exact Hsz _ (outgoing_sub_ids c)
  ihave Hvf := Hcback $$ Hc1
  have HarrEq : array.mk 2 ((tv.Config'.Voters'.arr.set (sint.Z (W64 0)).toNat vin).set
      (sint.Z (W64 1)).toNat vout) = tv.Config'.Voters' := by
    generalize tv.Config'.Voters' = a at Harr ⊢
    cases a
    simp only at Harr
    subst Harr
    rfl
  rw [HarrEq]
  ihave Htrk := Htrkback $$ Hvf
  wp_auto
  icases ownIdsetC_split _ _ _ $$ Hl with ⟨Hlq, %Hlc⟩
  wp_apply wp_MajorityConfig_Slice tv.Config'.Learners' c.learners $$ [Hlq]
    as %sl2 %xs2 ⟨Hlo, Hsl2, -, %Hxs2⟩
  · isplitl
    · unfold ownIdsetOpt; iapply ownIdsetQ_elim _ _ _ $$ Hlq
    · ipureintro; exact Hsz _ (learners_sub_ids c)
  icases ownIdsetC_split _ _ _ $$ Hln with ⟨Hlnq, %Hlnc⟩
  wp_apply wp_MajorityConfig_Slice tv.Config'.LearnersNext' c.learnersNext $$ [Hlnq]
    as %sl3 %xs3 ⟨Hlno, Hsl3, -, %Hxs3⟩
  · isplitl
    · unfold ownIdsetOpt; iapply ownIdsetQ_elim _ _ _ $$ Hlnq
    · ipureintro; exact Hsz _ (learnersNext_sub_ids c _ Hinv)
  -- the configuration back together
  ihave Hin : ownIdsetQ (GF := GF) vin (DFrac.own 1) c.incoming $$ [Hin]
  · unfold ownIdsetQ; iunfold ownIdsetOpt at Hin; iexact Hin
  ihave Hin := ownIdsetQ_not_nil _ _ _ Hvin_nn $$ Hin
  ihave Hoq : ownIdsetQ (GF := GF) vout (DFrac.own 1) c.outgoing $$ [Hoo]
  · unfold ownIdsetQ; iunfold ownIdsetOpt at Hoo; iexact Hoo
  ihave Hout := ownIdsetC_join _ _ _ Hoc $$ Hoq
  ihave Hlq : ownIdsetQ (GF := GF) tv.Config'.Learners' (DFrac.own 1) c.learners $$ [Hlo]
  · unfold ownIdsetQ; iunfold ownIdsetOpt at Hlo; iexact Hlo
  ihave Hl := ownIdsetC_join _ _ _ Hlc $$ Hlq
  ihave Hlnq : ownIdsetQ (GF := GF) tv.Config'.LearnersNext' (DFrac.own 1) c.learnersNext
      $$ [Hlno]
  · unfold ownIdsetQ; iunfold ownIdsetOpt at Hlno; iexact Hlno
  ihave Hln := ownIdsetC_join _ _ _ Hlnc $$ Hlnq
  ihave Hcfg := ownCfgCC_intro tv.Config' (DFrac.own 1) c vin vout Harr Hal Hwit $$ Hin Hout Hl Hln
  -- raft v3.7: `&pb.ConfState{..., AutoLeave: new(p.AutoLeave)}`; the `AutoLeave` cell is
  -- allocated (`«$v4»`), and the struct (`«$r0»`, raft#168: into the local `cs`)
  -- raft#168: `if p.Witnesses[0] != 0 {...}`, `if p.Witnesses[1] != 0 {...}`: both `0`, the
  -- fields stay `nil` (`notes/pr-verify/raft-168.md`)
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Witnesses"] ↦
        tv.Config'.Witnesses')
      (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Witnesses"] ↦
        tv.Config'.Witnesses')
      (P := trk ↦ tv)) $$ Htrk with ⟨HW, Htrkback⟩
  icases array_acc_same' _ (sint.Z (W64 0)) _ _ _ (W64 0) (by decide) (by rw [Hwit.1, hw]; rfl)
    $$ HW with ⟨Hw0, Hwback⟩
  wp_auto
  ihave HW := Hwback $$ Hw0
  icases array_acc_same' _ (sint.Z (W64 1)) _ _ _ (W64 0) (by decide) (by rw [Hwit.1, hw]; rfl)
    $$ HW with ⟨Hw1, Hwback⟩
  wp_auto
  ihave HW := Hwback $$ Hw1
  ihave Htrk := Htrkback $$ HW
  rw [← Hal]
  -- the fresh struct (hidden fields zero) into its ownership predicate (InvPb, stage R1)
  ihave %Hpn := typedPointsto_not_null $$ «$v4»
  imod cellRO_alloc _ _ $$ «$v4» with #cA
  imod csPts_of_struct «$r0_ptr»
    { state' := zeroValDef, Voters' := sl0, Learners' := sl2, VotersOutgoing' := sl1,
      LearnersNext' := sl3, AutoLeave' := «$v4_ptr», Witness' := null, WitnessOutgoing' := null,
      unknownFields' := slice.nil, sizeCache' := 0 }
    (ConfStateM.mk xs0 xs2 xs1 xs3 tv.Config'.AutoLeave') ⊤ rfl
    $$ [«$r0» Hsl0 Hsl2 Hsl1 Hsl3 cA] with «$r0»
  · iframe
    iframe cA
    isplitl <;> (simp only; unfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
  rw [show decide (_ ≠ null) = true from decide_eq_true Hpn]
  imodintro
  iapply HΦ
  iframe Htrk «$r0»
  isplitl [Hvotes Hprogs Hcfg]
  · iapply ownTrackerC_intro c tv votes prs pvs Hinv Hdom Hflags Hsize HmaxInfl Hnw
      $$ Hvotes Hprs Hprogs Hcfg Hepoch
  ipureintro
  rw [domSet_gset] at Hxs0 Hxs1 Hxs2 Hxs3
  exact ⟨Hxs0, Hxs1, Hxs2, Hxs3⟩

end proof

end EtcdGrove
end Perennial
