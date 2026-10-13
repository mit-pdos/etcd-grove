/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__answer.lean`.
Lean-first (no Rocq counterpart).

A read state whose index is at most `applied` (so at most `|ap|`) and whose context decodes
to this replica's read at `seq`, with a waiter in `reads`: the context is the one minted at
`(id, seq)` (`reg_read_minted`, from raft's read-context registry), so the waiter's record
(`readReq γ c Lc`) is the read state's (`readOk γ c i`): `Lc <+: ap` (`readOk_prefix`), and the
client data of `Lc` is a prefix of `ap`'s (`entDataIs_list_prefix`): the value after `ap`
answers it (`readP`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.decode
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

theorem firstOcc_prefix_of_prefix (a b : List (Option (List w8))) (h : a <+: b) :
    firstOcc a <+: firstOcc b := by
  obtain ⟨t, rfl⟩ := h
  exact firstOcc_append_prefix a t

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Register.answer.wp_proof (wp_decode : register.decode.spec (GF := GF) (hG := hG)) :
    Register.answer.spec (GF := GF) (hG := hG) := by
  intro γr γp r id n st ap psl ps dq applied Happ
  wp_start as ⟨#Hrep, Hrun, Hpsl, #Hps⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  wp_auto
  ihave %Hpslen := ownSlice_len $$ Hpsl
  ihave IH : iprop(∃ (k : w64) (rsv : ReadState) (restv : GoSlice) (ps' : List ReadState),
      "i" ∷ i_ptr ↦ k ∗ "rs" ∷ rs_ptr ↦ rsv ∗ "rest" ∷ rest_ptr ↦ restv ∗
      "Hrest" ∷ restv ↦* ps' ∗ "Hcap" ∷ ownSliceCap ReadState restv (DFrac.own 1) ∗
      "Hps'" ∷ ([∗list] s ∈ ps', readStateOk γr.raft s) ∗
      "Hrun" ∷ runOwn γr r ap ∗ "Hpsl" ∷ psl ↦*{dq} ps ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ps.length : Int)⌝) $$ [i rs rest Hrun Hpsl]
  · iexists W64 0, _, _, []
    iframe i rs rest Hrun Hpsl
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ps.length := by word
    obtain ⟨sv, Hsv⟩ : ∃ sv, ps[sint.nat k]? = some sv := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z psl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index psl (sint.Z k) _ dq sv Hk.1 $$ [Hpsl] as Hpsl
    · iframe Hpsl; ipureintro; exact Hsv
    ihave #Hsv := BigSepL.bigSepL_lookup (Φ := fun _ s => readStateOk (GF := GF) γr.raft s) Hsv
      $$ Hps
    wp_if_destruct
    · -- a later index: kept
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hrest $Hcap $Hsl1] as %rest' ⟨Hrest, Hcap, -⟩
      wp_for_post
      iframe
      iexists k + W64 1, sv, rest', ps' ++ [sv]
      iframe
      isplitl
      · iapply (BigSepL.bigSepL_singleton (Φ := fun _ s => readStateOk (GF := GF) γr.raft s)).2
        iexact Hsv
      ipureintro; constructor <;> word
    · -- answered, if it is this replica's waiting read
      have Hle : uint.Z sv.Index' ≤ (ap.length : Int) := by word
      imod node_readState_data γp.node id n sv ⊤ CoPset.subseteq_top $$ HisNode [] with
        ⟨%cx, #Hcx, #Hok⟩
      · rw [Hraft]; iexact Hsv
      rw [Hraft]
      wp_apply wp_decode sv.RequestCtx' cx DFrac.discard $$ [$Hcx]
      iintro -
      cases Hdec : decodeOp cx with
      | none =>
        simp only [decodeRet, Hdec]
        wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, sv, restv, ps'
        iframe
        ipureintro; constructor <;> word
      | some x =>
        obtain ⟨rep, sq, kd, vl⟩ := x
        simp only [decodeRet, Hdec]
        wp_auto
        have Hkey : opKey cx = some (rep, sq) := by simp [opKey, Hdec]
        wp_if_destruct
        · wp_if_destruct
          · -- this replica's read
            wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
            iNamed HR
            iunfold readsOwn at Hrds
            iNamed Hrds
            iunfold runOwn at Hrun
            iNamed Hrun
            wp_auto
            wp_apply wp_map_lookup2 go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string)
              mR Rd sq (DFrac.own 1) $$ [$HRd] as HRd
            ihave Hrun : iprop(r.[RRegister, go!"value"] ↦ v -∗ r.[RRegister, go!"applied"] ↦ mA -∗
                mA ↦$ A -∗ runOwn γr r ap) $$ []
            · iintro Hv HmA HA
              unfold runOwn
              iexists v, mA, A, ods
              iframe Hv HmA HA Hap Hods
              ipureintro; exact ⟨Hval, HA⟩
            cases HRs : Rd !! sq with
            | none =>
              simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
              wp_auto
              wp_apply sync.Mutex.wp_Unlock _ _
                $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters HmR HRd Hreads]
              · inext
                unfold lockInv
                iexists ns, mW, W, c
                iframe
                isplitr
                · ipureintro; exact Hc
                isplitr
                · ipureintro; exact HWdom
                unfold readsOwn
                iexists mR, Rd
                iframe
                ipureintro; exact HRdom
              ihave Hrun := Hrun $$ Hv HmA HA
              wp_for_post
              iframe
              iexists k + W64 1, sv, restv, ps'
              iframe
              ipureintro; constructor <;> word
            | some ch =>
              simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
              wp_auto
              wp_apply wp_mapDelete mR Rd sq go.uint64
                (go.GoType.ChannelType go.ChanDir.sendrecv go.string) $$ [$HRd] as HRd
              icases (BigSepM.bigSepM_delete (Φ := fun s ch => readWaiterOk (GF := GF) γr id s ch)
                HRs).1 $$ Hreads with ⟨Hw, Hreads⟩
              iunfold readWaiterOk at Hw
              icases Hw with ⟨%c0, %Lc, %odsc, %γh, #Hmint, #Hrq, #Hodsc, #Hho, Hprod⟩
              iunfold readOk at Hok
              icases Hok with ⟨%Lc', #Hrq', %HLc'⟩
              ihave #Hrq'2 := Hrq'
              iunfold readReq at Hrq'2
              icases Hrq'2 with ⟨#Hrel, -⟩
              rw [Hif] at Hkey
              imod reg_read_minted γr cx c0 Lc' (id, sq) ⊤ CoPset.subseteq_top Hkey
                $$ Hinv Hrel Hmint with %Hc0
              subst Hc0
              icases readReq_agree γr.raft c0 Lc' Lc $$ Hrq' Hrq with %HLL
              subst HLL
              ihave %Hpre := readOk_prefix γr.raft c0 sv.Index' Lc' ap Hle $$ [] Hrq Hap
              · unfold readOk
                iexists Lc'
                iframe Hrq
                ipureintro; exact HLc'
              ihave %Hpre2 := entDataIs_list_prefix _ Lc' ap odsc ods Hpre $$ Hodsc Hods
              wp_apply sync.Mutex.wp_Unlock _ _
                $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters HmR HRd Hreads]
              · inext
                unfold lockInv
                iexists ns, mW, W, c
                iframe
                isplitr
                · ipureintro; exact Hc
                isplitr
                · ipureintro; exact HWdom
                unfold readsOwn
                iexists mR, GMap.delete sq Rd
                iframe
                ipureintro
                intro s ch' Hs
                by_cases Hss : s = sq
                · subst Hss; rw [GMap.lookup_delete_eq] at Hs; cases Hs
                · rw [GMap.lookup_delete_ne _ (Ne.symm Hss)] at Hs; exact HRdom s ch' Hs
              wp_apply wp_handoff_send (t := go.string) γh ch (readP γr (firstOcc odsc)) iprop(True)
                iprop(False) v $$ [$Hho $Hprod]
              · isplitl
                · unfold readP
                  iexists firstOcc ods
                  isplitl
                  · unfold regLb
                    iexists ap, ods
                    iframe Hap Hods
                    ipureintro; rfl
                  ipureintro; exact ⟨firstOcc_prefix_of_prefix _ _ Hpre2, Hval⟩
                · itrivial
              iintro -
              wp_auto
              ihave Hrun := Hrun $$ Hv HmA HA
              wp_for_post
              iframe
              iexists k + W64 1, sv, restv, ps'
              iframe
              ipureintro; constructor <;> word
          · -- not a read
            wp_for_post
            iframe
            iexists k + W64 1, sv, restv, ps'
            iframe
            ipureintro; constructor <;> word
        · -- another replica's
          wp_for_post
          iframe
          iexists k + W64 1, sv, restv, ps'
          iframe
          ipureintro; constructor <;> word
  · iapply HΦ
    iframe

end proof

end register
end EtcdGrove
end Perennial
