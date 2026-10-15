/- Lean-first (no Rocq counterpart), 2026-10-13; 2026-10-15 (stage N): the dynamic mode. -/
module

public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.ApplyConfChange.wp_proof
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG)) :
    node.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  intro γ id n c o ds ca cfg k e cs' Hshr Hdyn
  wp_start as ⟨#Hnode, Hc, HR⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  have Hmode : γ.mode = .static ∨ ∃ dec c0 h0 h1, γ.mode = .dyn dec c0 h0 h1 := by
    cases h : γ.mode with
    | static => exact .inl rfl
    | dyn dec c0 h0 h1 => exact .inr ⟨dec, c0, h0, h1, rfl⟩
  rcases o with m | m
  · simp only [ownCCI, ownCCV1]
    icases Hc with ⟨%v, %Hcv, %Hvm, -⟩
    subst Hcv
    obtain ⟨Hty, Hnid, -⟩ := Hvm
    wp_auto
    wp_apply +noauto wp_ConfChange_AsV2 as %v2 ⟨%Hv2, Hch⟩
    imod ownSlice_persist $$ Hch with #Hch
    generalize Hccs : [({ Type' := v.Type', NodeId' := v.NodeId' } : raftpb.ConfChangeSingle)] = ccs

    have Hvo : (v2.Transition', ccs) = ccV2Of (.v1 m) := by
      rw [← Hccs, Hv2.1, Hty, Hnid]; rfl
    -- the payload, by the mode; the driver keeps the answer slot's other half
    ihave Hpay : iprop(|==> (confcP γ v2 ∗ (⌜γ.mode = .static⌝ ∨ (⌜γ.mode.isDyn = true⌝ ∗
        dghostVar γ.ccq (DFrac.own (1 : Qp).half) (k + 1, cs'))))) $$ [HR]
    · rcases Hmode with hm | ⟨dec, c0, h0, h1, hm⟩
      · imodintro
        isplitl []
        · unfold confcP
          iexists ccs
          iframe Hch
          ileft
          ipureintro
          exact ⟨hm, by have H := Hshr hm; rw [← Hvo] at H; exact H⟩
        ileft; ipureintro; exact hm
      · icases HR with (%Hs | ⟨Hcfg, #Hdlb⟩)
        · rw [hm] at Hs; cases Hs
        unfold nodeCfg
        icases Hcfg with ⟨Hcap, ⟨%x, Hq1, Hq2⟩, #Hcamlb⟩
        imod dghostVar_update_halves (k + 1, cs') γ.ccq x x $$ Hq1 Hq2 with ⟨Hq1, Hq2⟩
        imodintro
        isplitl [Hcap Hq1]
        · unfold confcP
          iexists ccs
          iframe Hch
          iright
          iexists ds, ca, cfg, k, e, cs'
          unfold dlvLb
          iframe Hdlb Hcap Hq1
          ipureintro
          refine ⟨by rw [hm]; rfl, fun dec' c0' h0' h1' hm' => ?_⟩
          rw [Hvo]; exact Hdyn dec' c0' h0' h1' hm'
        iright
        iframe Hq2
        ipureintro; rw [hm]; rfl
    imod Hpay with ⟨HP, Hkeep⟩
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists raftpb.ConfChangeV2, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.confc', γ.confc, _
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hconfc
      iapply handshake_send_au γ.confc nv.confc' _ (confcP γ) iprop(True)
        $$ [$Hlc1 $Hlc2 $Hlc3] Hconfc HP
      inext
      iintro -
      wp_auto_lc 2
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists raftpb.ConfState, inferInstance, inferInstance, inferInstance, inferInstance,
          nv.confstatec', γ.confstatec
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hconfstatec
        iapply handshake_receive_au γ.confstatec nv.confstatec' (confstateP γ) iprop(True) _
          $$ [$Hlc1 $Hlc2] Hconfstatec []
        · itrivial
        inext
        iintro %csv Hcs
        wp_auto
        iapply HΦ
        iunfold confstateP at Hcs
        icases Hcs with (⟨%Hs, Hcs⟩ | ⟨%Hd, %w, Hcap, Hq, #Hlb, Hok⟩)
        · icases Hkeep with (%Hs' | ⟨%Hd', -⟩)
          · iframe
            ileft
            iframe Hcs
            ipureintro; exact Hs
          · rw [Hs] at Hd'; cases Hd'
        · icases Hkeep with (%Hs' | ⟨%Hd', Hq'⟩)
          · rw [Hs'] at Hd; cases Hd
          ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hq Hq'
          subst Heq
          iframe
          iright
          isplitr
          · ipureintro; exact Hd
          iframe Hok
          unfold nodeCfg
          iframe Hcap Hlb
          iexists (k + 1, cs')
          iframe Hq Hq'
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hdone
        iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
      iapply BigAndL.bigAndL_nil.2
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · simp only [ownCCI, ownCCV2]
    icases Hc with ⟨%v, %Hcv, %Htr, #Hch, -⟩
    subst Hcv
    wp_auto
    wp_apply +noauto wp_ConfChangeV2_AsV2
    generalize Hccs : m.changes = ccs
    have Hvo : (v.Transition', ccs) = ccV2Of (.v2 m) := by
      rw [← Hccs, Htr]; rfl
    -- the payload, by the mode; the driver keeps the answer slot's other half
    ihave Hpay : iprop(|==> (confcP γ v ∗ (⌜γ.mode = .static⌝ ∨ (⌜γ.mode.isDyn = true⌝ ∗
        dghostVar γ.ccq (DFrac.own (1 : Qp).half) (k + 1, cs'))))) $$ [HR]
    · rcases Hmode with hm | ⟨dec, c0, h0, h1, hm⟩
      · imodintro
        isplitl []
        · unfold confcP
          iexists ccs
          iframe Hch
          ileft
          ipureintro
          exact ⟨hm, by have H := Hshr hm; rw [← Hvo] at H; exact H⟩
        ileft; ipureintro; exact hm
      · icases HR with (%Hs | ⟨Hcfg, #Hdlb⟩)
        · rw [hm] at Hs; cases Hs
        unfold nodeCfg
        icases Hcfg with ⟨Hcap, ⟨%x, Hq1, Hq2⟩, #Hcamlb⟩
        imod dghostVar_update_halves (k + 1, cs') γ.ccq x x $$ Hq1 Hq2 with ⟨Hq1, Hq2⟩
        imodintro
        isplitl [Hcap Hq1]
        · unfold confcP
          iexists ccs
          iframe Hch
          iright
          iexists ds, ca, cfg, k, e, cs'
          unfold dlvLb
          iframe Hdlb Hcap Hq1
          ipureintro
          refine ⟨by rw [hm]; rfl, fun dec' c0' h0' h1' hm' => ?_⟩
          rw [Hvo]; exact Hdyn dec' c0' h0' h1' hm'
        iright
        iframe Hq2
        ipureintro; rw [hm]; rfl
    imod Hpay with ⟨HP, Hkeep⟩
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists raftpb.ConfChangeV2, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.confc', γ.confc, _
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hconfc
      iapply handshake_send_au γ.confc nv.confc' _ (confcP γ) iprop(True)
        $$ [$Hlc1 $Hlc2 $Hlc3] Hconfc HP
      inext
      iintro -
      wp_auto_lc 2
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists raftpb.ConfState, inferInstance, inferInstance, inferInstance, inferInstance,
          nv.confstatec', γ.confstatec
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hconfstatec
        iapply handshake_receive_au γ.confstatec nv.confstatec' (confstateP γ) iprop(True) _
          $$ [$Hlc1 $Hlc2] Hconfstatec []
        · itrivial
        inext
        iintro %csv Hcs
        wp_auto
        iapply HΦ
        iunfold confstateP at Hcs
        icases Hcs with (⟨%Hs, Hcs⟩ | ⟨%Hd, %w, Hcap, Hq, #Hlb, Hok⟩)
        · icases Hkeep with (%Hs' | ⟨%Hd', -⟩)
          · iframe
            ileft
            iframe Hcs
            ipureintro; exact Hs
          · rw [Hs] at Hd'; cases Hd'
        · icases Hkeep with (%Hs' | ⟨%Hd', Hq'⟩)
          · rw [Hs'] at Hd; cases Hd
          ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hq Hq'
          subst Heq
          iframe
          iright
          isplitr
          · ipureintro; exact Hd
          iframe Hok
          unfold nodeCfg
          iframe Hcap Hlb
          iexists (k + 1, cs')
          iframe Hq Hq'
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hdone
        iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
      iapply BigAndL.bigAndL_nil.2
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
