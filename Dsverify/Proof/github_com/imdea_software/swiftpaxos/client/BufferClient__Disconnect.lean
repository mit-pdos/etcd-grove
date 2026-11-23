/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/BufferClient__Disconnect.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Disconnect
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.CodecG

-- PORT: lab imports dropped: Harness.Spec.net.TCPConn__Close

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [client.Assumptions]
-- the codec (decision D6, Proof/swiftnet/KitLike.lean)
variable [C : net.rpc.RpcCodec netDistGF]

/-- `Disconnect` over the codec `C` (`Disconnect.specG`, Proof/client/CodecG.lean). -/
theorem client.BufferClient.Disconnect.wp_proofG
    (wp_Close : net.rpc.Client.Close.spec (GF := netDistGF) (hG := hG))
    (wp_TCPClose : net.TCPConn.Close.spec (GF := netDistGF) (hG := hG)) :
    client.BufferClient.Disconnect.specG (hG := hG) := by
  intro b
  wp_start as Hf
  ihave Hf := (client.failedG_unfold _).1 $$ Hf
  icases Hf with ⟨%bv, %v, #Hb, Hcl, #Hq, %Hnn, Hm, %srvs, Hsrvs, Hss⟩
  ihave #Hbf := Hb
  iStructNamed Hbf
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsrvs
  ihave HI : (∃ (i : w64) (sv : GoInterface), "i" ∷ i_ptr ↦ i ∗ "s" ∷ s_ptr ↦ sv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.servers'.len⌝ : IProp netDistGF) $$ [i s]
  · iexists _, _; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hiN : sint.nat i < srvs.length := by word
    list_elem srvs (sint.nat i) as sv
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by word⟩)]
    wp_apply wp_load_slice_index _ (sint.Z i) srvs (DFrac.own 1) sv Hi.1 $$ [Hsrvs] as Hsrvs
    · iframe; ipureintro; exact Hsv_lookup
    ihave Hacc := (BigSepL.bigSepL_lookup_acc Hsv_lookup).1 $$ Hss
    icases Hacc with ⟨Hsv, Hback⟩
    icases Hsv with (%Hnil | ⟨%cn, %side, #Hconn⟩)
    · subst Hnil
      wp_auto
      ihave Hss := Hback $$ [] 
      · ileft; ipureintro; rfl
      rw [list_set_lookup_self srvs (sint.nat i) _ Hsv_lookup]
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; word
    · iunfold net.rpc.connIface at Hconn
      icases Hconn with ⟨%tc, %Htc, #Hown⟩
      subst Htc
      wp_auto
      wp_apply wp_TCPClose tc cn side $$ [$Hown] as %err -
      ihave Hss := Hback $$ []
      · iright; iexists cn, side; iunfold net.rpc.connIface; iexists tc; iframe #; ipureintro; rfl
      rw [list_set_lookup_self srvs (sint.nat i) _ Hsv_lookup]
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; word
  · icases Hm with (%Hm | ⟨%W, %a, #Hmc⟩)
    · rw [decide_eq_true Hm]
      wp_auto
      iapply HΦ; itrivial
    · by_cases hm : v.master' = null
      · rw [decide_eq_true hm]
        wp_auto
        iapply HΦ; itrivial
      rw [decide_eq_false hm]
      wp_auto
      wp_apply wp_Close v.master' W a $$ [$Hmc] as %err -
      iapply HΦ; itrivial

end proof

section frozen
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [client.Assumptions]

/-- The frozen statement: `Disconnect.wp_proofG` at `kitCodec`. -/
theorem client.BufferClient.Disconnect.wp_proof
    (wp_Close : net.rpc.Client.Close.spec (GF := netDistGF) (hG := hG))
    (wp_TCPClose : net.TCPConn.Close.spec (GF := netDistGF) (hG := hG)) :
    client.BufferClient.Disconnect.spec (hG := hG) :=
  client.BufferClient.Disconnect.spec_of_G
    (client.BufferClient.Disconnect.wp_proofG wp_Close wp_TCPClose)

end frozen

end Perennial.github_com.imdea_software.swiftpaxos
