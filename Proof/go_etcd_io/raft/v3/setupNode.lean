/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.setupNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `len(peers) == 0` dead (`ps ≠ []`); `NewRawNode` (no error); `Bootstrap` (no error, so no
warning); `newNode`. -/
theorem setupNode.wp_proof
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_RawNode_Bootstrap : RawNode.Bootstrap.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG)) :
    setupNode.spec (GF := GF) (hG := hG) := by
  intro γ md c cv lok si sn σ hs csm R R' peers dq pv ps ctxs bootLog P1 P2 P3 P4 P5 P6 P7 P8 P9 P10
    S1 S2 S3 S4 S5 S6 Hhs Q1 Q2 Q3 Q4 Q5 Hfl0 Hun R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
  wp_start as ⟨Hc, #Hlg, HR, #HFI, #HLI, #HIS, Hpeers, #Hctx, #Hmarshal, Hghost, #Hcommitted, #Hcl⟩
  ihave %Hplen := ownSlice_len $$ Hpeers
  have Hpvne : pv ≠ [] := by
    intro h; apply R2; rw [R1, h]; rfl
  have Hca : committedAfter σ.prev hs = W64 0 := by
    unfold committedAfter; rw [if_pos Hhs, S1]
  have Hca0 : uint.nat (committedAfter σ.prev hs) = 0 := by rw [Hca]; rfl
  have Hp0 : uint.nat σ.prev.index' = 0 := by rw [S1]; rfl
  wp_auto
  wp_if_destruct
  · exfalso
    have h0 : pv.length = 0 := by
      have := Hplen.1; rw [this]; word
    exact Hpvne (List.eq_nil_of_length_eq_zero h0)
  have HAR : AttachRec sn σ.prev σ.ents (uint.nat (committedAfter σ.prev hs))
      (max (uint.nat σ.prev.index') (uint.nat cv.Applied')) := by
    rw [Hca0, Hp0, P10]
    refine ⟨by rw [← Hun]; rfl, by rw [← Hun]; rfl, fun i t h _ => ?_, fun i h1 h2 => by omega⟩
    rw [← Hun] at h; exact absurd h List.not_mem_nil
  have A1 : LogIndicesOk σ.prev σ.ents := by rw [S2]; intro k e h; simp at h
  have A2 : uint.nat σ.prev.index' ≤ σ.fr := by rw [S4, Hp0]; exact Nat.le_refl _
  have A3 : σ.fr ≤ uint.nat (committedAfter σ.prev hs) := by rw [S4]; exact Nat.zero_le _
  have A4 : uint.Z σ.fl ≤ uint.Z σ.prev.index' := by rw [Hfl0, S1]; exact Int.le_refl _
  have A5 : σ.sg ≤ uint.nat σ.prev.index' := by rw [S5]; exact Nat.zero_le _
  have A10 : ConfStateOk csm := by
    refine ⟨.inr ⟨Q1, Q2, Q3, Q4⟩, ?_, ?_, ?_, ?_, fun _ => Q5⟩ <;>
      first | (rw [Q1]; exact List.nodup_nil) | (rw [Q2]; exact List.nodup_nil)
        | (rw [Q3]; exact List.nodup_nil) | (rw [Q4]; exact List.nodup_nil)
  have A7 : uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64 := by
    rw [S1, S2]; simp only [List.length_nil]; have : uint.Z (W64 0) = 0 := rfl; omega
  have A8 : restoreM csm.VotersOutgoing' csm.Voters' csm.Learners' csm.LearnersNext' csm.AutoLeave' =
      some (cfgState ∅ ∅) := by rw [Q2, Q1, Q3, Q4]; rfl
  have A9 : csm.Voters'.length + csm.VotersOutgoing'.length + csm.Learners'.length +
      csm.LearnersNext'.length ≤ 2 ^ 62 := by rw [Q1, Q2, Q3, Q4]; simp
  wp_apply wp_NewRawNode c cv lok si sn σ hs csm R R' (cfgState ∅ ∅) P1 P2 P3 P4 P5 P6 P7 P8 P9
    A1 S3 A2 A3 A4 A5 S6 A7 HAR (.inl Hhs) (.inl P10) A8 A9 A10
    $$ [Hc HR]
    as %rn %err ⟨HR', %s, Hfresh, %Herr, %Hsn2⟩
  · iframe Hc Hlg HR
    isplitr
    · iintro !> !>
      iExactEq HFI; rw [S1]; rfl
    isplitr
    · iintro !> !>
      iExactEq HLI; rw [S1, S2]; rfl
    rw [Hun]; iexact HIS
  subst Herr
  obtain ⟨-, Hgsn⟩ := Hsn2
  subst Hgsn
  wp_auto
  have Hfresh0 : GMap.listToSet csm.Voters' = ∅ := by rw [Q1]; rfl
  ihave Hfresh := rawNodeAt_fresh rn cv.ID' si ∅ cv.StepDownOnRemoval' cv.PreVote' hs σ cv.Applied' s
    Hhs S1 S2 P10 $$ Hfresh
  wp_apply wp_RawNode_Bootstrap γ md rn cv.ID' si cv.StepDownOnRemoval' cv.PreVote' s peers dq pv ps
    ctxs bootLog R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
    $$ [$Hfresh $Hpeers $Hctx $Hmarshal $Hghost $Hcommitted $Hcl] as %err2 ⟨%Herr2, Hrn, Hpeers⟩
  subst Herr2
  wp_auto
  wp_apply wp_newNode rn as %nv ⟨%Hnvrn, Hchans⟩
  iapply HΦ
  iframe HR'
  iexists nv, rn
  iframe n Hchans Hrn Hpeers
  ipureintro; exact Hnvrn

end proof

end EtcdGrove
end Perennial
