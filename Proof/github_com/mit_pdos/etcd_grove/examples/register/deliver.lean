/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/deliver.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.transfers__take
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.deliverable
public import Spec.go_etcd_io.raft.v3.node__Step

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [StorageModel GF]

theorem deliver.wp_proof (wp_deliverable : deliverable.spec (GF := GF) (hG := hG))
    (wp_take : transfers.take.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG)) :
    deliver.spec (GF := GF) (hG := hG) := by
  intro γ bud peers tr P msl ms Hcfg
  wp_start as ⟨#Hpeers, #HP, #Htr, Hms, #Hmsok, Hcr⟩
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  ihave %Hmslen := ownSlice_len $$ Hms
  ihave IH : iprop(∃ (k : w64) (mv : raftpb.Message),
      "i" ∷ i_ptr ↦ k ∗ "m" ∷ m_ptr ↦ mv ∗ "Hms" ∷ msl ↦* ms ∗
      "Hcr" ∷ ([∗list] m ∈ ms.drop (sint.nat k),
        rdCred γ (if m.Type' = MsgReadIndex then 1 else 0)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ms.length : Int)⌝) $$ [i m Hms Hcr]
  · iexists W64 0, _
    iframe i m Hms
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe Hcr
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ms.length := by word
    obtain ⟨mm, Hmm⟩ : ∃ mm, ms[sint.nat k]? = some mm := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z msl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index msl (sint.Z k) _ (DFrac.own 1) mm Hk.1 $$ [Hms] as Hms
    · iframe Hms; ipureintro; exact Hmm
    ihave ⟨#Hmok, #Hmlb⟩ := BigSepL.bigSepL_lookup (Φ := fun _ m =>
      iprop(isRaftMsg (GF := GF) γ m ∗ termLB bud m.Term')) Hmm $$ Hmsok
    -- the message's read credit
    have Hdrop : ms.drop (sint.nat k) = mm :: ms.drop (sint.nat k + 1) := by
      rw [List.drop_eq_getElem_cons Hlt]
      rw [List.getElem?_eq_getElem Hlt] at Hmm
      rw [Option.some.inj Hmm]
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [Hdrop]
    icases Hcr with ⟨Hc1, Hcr⟩
    wp_apply wp_deliverable mm as %b %Hb
    cases b
    · wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, mm
      rw [Hk1]
      iframe
      ipureintro; constructor <;> word
    have Hd := Hb rfl
    wp_auto
    wp_apply wp_map_lookup2 go.uint64 _ peers P mm.To' DFrac.discard $$ Hpeers as -
    cases HPt : P !! mm.To' with
    | none =>
      try simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, mm
      rw [Hk1]
      iframe
      ipureintro; constructor <;> word
    | some nd =>
      ihave #Hpeer := BigSepM.bigSepM_lookup (Φ := fun id nd => peerOk (GF := GF) γ bud id nd)
        HPt $$ HP
      unfold peerOk
      icases Hpeer with ⟨%γn, %n, %Hnd, #HisNode⟩
      obtain ⟨Hr, Hbud, rfl⟩ := Hnd
      icases raftMsg_deliverable γ mm Hd $$ Hmok with
        ⟨%ents, %ctx, %Hnil, #Hents, #Hctx, #Hmsg⟩
      try simp only [Option.isSome_some, Option.getD_some, _root_.decide_true, Bool.not_true]
      wp_auto
      subst Hr Hbud
      -- a `MsgTimeoutNow`: a tick credit from the transfer budget, or dropped
      by_cases Htn : mm.Type' = W32 14
      · rw [decide_eq_true Htn]
        wp_auto
        wp_apply wp_take γn.bud tr $$ [$Htr] as %b Hb
        cases b
        · wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, mm
          rw [Hk1]
          iframe
          ipureintro; constructor <;> word
        wp_auto
        ihave Htc : tickCred γn.bud (if mm.Type' = MsgTimeoutNow then 1 else 0) $$ [Hb]
        · have Htn' : mm.Type' = MsgTimeoutNow := Htn
          rw [if_pos Htn']
          simp only [↓reduceIte]
          iexact Hb
        wp_apply wp_slice_append slice.nil ([] : List raftpb.Entry) mm.Entries' ents DFrac.discard
          $$ [Hents] as %s' ⟨Hs, Hcap, -⟩
        · iframe Hents
          isplitl
          · iapply ownSlice_nil
          · iapply ownSliceCap_nil
        rw [List.nil_append]
        wp_apply context.wp_Background
        imod stepP_deliverable γn mm.To' mm ents ctx s' Hd rfl Hnil Hcfg
          $$ Hmsg Hctx Hmlb Hs Hcap Hc1 Htc with Hstep
        wp_apply wp_node_Step γn mm.To' n _ $$ [$Hraftinit $HisNode $Hstep] as %err -
        wp_for_post
        iframe
        iexists k + W64 1, _
        rw [Hk1]
        iframe
        ipureintro; constructor <;> word
      · rw [decide_eq_false Htn]
        wp_auto
        imod tickCred_zero (GF := GF) γn.bud with Htc0
        ihave Htc : tickCred γn.bud (if mm.Type' = MsgTimeoutNow then 1 else 0) $$ [Htc0]
        · have Htn' : ¬ mm.Type' = MsgTimeoutNow := Htn
          rw [if_neg Htn']
          iexact Htc0
        wp_apply wp_slice_append slice.nil ([] : List raftpb.Entry) mm.Entries' ents DFrac.discard
          $$ [Hents] as %s' ⟨Hs, Hcap, -⟩
        · iframe Hents
          isplitl
          · iapply ownSlice_nil
          · iapply ownSliceCap_nil
        rw [List.nil_append]
        wp_apply context.wp_Background
        imod stepP_deliverable γn mm.To' mm ents ctx s' Hd rfl Hnil Hcfg
          $$ Hmsg Hctx Hmlb Hs Hcap Hc1 Htc with Hstep
        wp_apply wp_node_Step γn mm.To' n _ $$ [$Hraftinit $HisNode $Hstep] as %err -
        wp_for_post
        iframe
        iexists k + W64 1, _
        rw [Hk1]
        iframe
        ipureintro; constructor <;> word
  · iapply HΦ; itrivial

end proof

end register
end EtcdGrove
end Perennial
