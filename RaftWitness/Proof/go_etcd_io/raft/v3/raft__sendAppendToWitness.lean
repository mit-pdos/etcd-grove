/-
Proof of `Spec/go_etcd_io/raft/v3/raft__sendAppendToWitness.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__sendAppendToWitness
public import Spec.go_etcd_io.raft.v3.tracker.ReplicationSet__GetNonWitnessVoterSlice

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The epoch's halves' voter slices (`GetNonWitnessVoterSlice`, frozen read-only), the request
built and appended to the queue (`ownRaftPhysC_witQ`), then the `Infof`. -/
theorem raft.sendAppendToWitness.wp_proof
    (wp_GetNonWitnessVoterSlice :
      tracker.ReplicationSet.GetNonWitnessVoterSlice.spec (GF := GF) (hG := hG)) :
    raft.sendAppendToWitness.spec (GF := GF) (hG := hG) := by
  intro c r id s w i st Hw Hwc
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_load_trk_EpochC' c r id s $$ Hphys as %e ⟨Hphys, #He⟩
  iunfold ownEpochOk at He
  icases He with ⟨#He, -⟩
  icases ownEpoch_fields _ _ $$ He with ⟨-, ⟨%r0, #Hr0, #Hrs0⟩, ⟨%r1, #Hr1, #Hrs1⟩⟩
  try wp_auto
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  try wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  try wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  try wp_auto
  wp_apply wp_GetNonWitnessVoterSlice _ r0 _ $$ [$Hr0 $Hrs0] as %sl0 %xs0 ⟨Hsl0, Hcap0, %Hxs0⟩
  try wp_auto
  wp_apply wp_GetNonWitnessVoterSlice _ r1 _ $$ [$Hr1 $Hrs1] as %sl1 %xs1 ⟨Hsl1, Hcap1, %Hxs1⟩
  try wp_auto
  -- the request, read-only (`ownWMsg`)
  imod ownSlice_persist $$ Hsl0 with #Hsl0
  imod ownSlice_persist $$ Hsl1 with #Hsl1
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnil with #Hnil
  -- `r.witnessMsgs = append(r.witnessMsgs, msg)`
  icases ownRaftPhysC_witQ c r id s $$ Hphys with ⟨%wsl, %μs, HT, Hwf, Hq, Hback⟩
  iunfold ownWQueue at Hq
  icases Hq with ⟨%wms, Hqs, Hqcap, #Hqm⟩
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %m_sl ⟨m_sl, -⟩
  try wp_auto
  wp_apply wp_slice_append $$ [Hqs Hqcap m_sl] as %q' ⟨Hqs, Hqcap, -⟩
  · iframe
  try wp_auto
  ihave Hq : ownWQueue (GF := GF) q' (μs ++ [wappMsg id w s.term st i xs0 xs1]) $$ [Hqs Hqcap]
  · iunfold ownWQueue
    iexists _
    iframe Hqs Hqcap
    iapply BigSepL2.bigSepL2_snoc.2
    iframe Hqm
    unfold ownWMsg
    simp only [wappMsg]
    iexists sl0, sl1
    iframe Hsl0 Hsl1 Hnil
    isplitr
    · ipureintro; simp only [MsgApp, and_true]
    ileft; ipureintro; exact ⟨rfl, trivial⟩
  ihave Hphys := Hback $$ %q' %_ %Hw %(⟨Hwc, rfl, fun _ => Int.le_refl _⟩) HT Hwf Hq
  -- the `Infof`
  try wp_auto
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  try wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  try wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  try wp_auto
  wp_raft_logC
  iapply HΦ $$ %xs0 %xs1
  iframe Hphys
  ipureintro; exact ⟨Hxs0, Hxs1⟩

end proof

end EtcdGrove
end Perennial
