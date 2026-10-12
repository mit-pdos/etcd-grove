/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__processMessages.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__processMessages
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Warn
public import Perennial.Proof.fmt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftNode.processMessages.wp_proof
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    raftNode.processMessages.spec (GF := GF) (hG := hG) := by
  intro E γ r sl msL
  wp_start as ⟨#Hr, #Hsl, #Hall⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave #Hr' := Hr
  iunfold isRaftNode at Hr'
  iNamed Hr'
  wp_auto
  ihave IH : iprop(∃ (k : w64) (out : GoSlice) (outL : List Loc) (b : Bool),
      "r" ∷ r_ptr ↦ r ∗ "ms" ∷ ms_ptr ↦ sl ∗ "i" ∷ i_ptr ↦ k ∗
      "messages" ∷ messages_ptr ↦ out ∗ "Hout" ∷ out ↦* outL ∗
      "Hcap" ∷ ownSliceCap Loc out (DFrac.own 1) ∗ "Houtok" ∷ ([∗list] m ∈ outL, rnMsgOk E m) ∗
      "sentAppResp" ∷ sentAppResp_ptr ↦ b ∗
      "%Hk" ∷ ⌜-1 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len⌝) $$ [r ms i messages sentAppResp]
  · iexists sl.len - W64 1, slice.nil, [], false
    iframe r ms i sentAppResp
    isplitl [messages]
    · iexact messages
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; constructor <;> word
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_for IH
  wp_if_destruct
  · have hk0 : 0 ≤ sint.Z k := by word
    have hkl : (sint.Z k).toNat < msL.length := by rw [Hlen.1]; word
    obtain ⟨m, hm⟩ : ∃ m, msL[(sint.Z k).toNat]? = some m :=
      ⟨_, List.getElem?_eq_getElem hkl⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index sl (sint.Z k) msL DFrac.discard m (by word) $$ [] as -
    · iframe Hsl; ipureintro; exact hm
    ihave #Hm := (BigSepL.bigSepL_lookup (Φ := fun _ m => rnMsgOk E m) hm) $$ Hall
    iunfold rnMsgOk at Hm
    icases Hm with ⟨%to, %ty, #Hmat, #HM⟩
    wp_apply wp_GetTo m to ty $$ [$Hrpb $Hmat]
    iunfold isRNIDRemoved at Hidri
    ispecialize Hidri $$ %to
    wp_apply Hidri as %rm -
    wp_if_destruct
    rotate_left
    · -- removed member: `continue`
      wp_for_post
      iframe HΦ
      iexists k - W64 1, out, outL, b
      iframe
      ipureintro; constructor <;> word
    wp_apply wp_GetType m to ty $$ [$Hrpb $Hmat]
    wp_if_destruct
    · -- `MsgAppResp`: only the last one
      cases b
      rotate_left
      · wp_for_post
        iframe HΦ
        iexists k - W64 1, out, outL, true
        iframe
        ipureintro; constructor <;> word
      wp_auto
      wp_apply wp_GetType m to _ $$ [$Hrpb $Hmat]
      wp_if_destruct
      · exact absurd Hif (by decide)
      wp_apply wp_GetType m to _ $$ [$Hrpb $Hmat]
      wp_if_destruct
      · exact absurd Hif (by decide)
      done
    · done
  · iapply HΦ
    iexists outL
    iframe Hout Houtok

end proof

end EtcdGrove
end Pere