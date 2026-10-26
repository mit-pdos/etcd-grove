/- Lean-first (no Rocq counterpart), 2026-10-13; 2026-10-15 (stage N): the dynamic mode. -/
module

public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import Proof.go_etcd_io.raft.v3.LemmasNodeR
public import Proof.go_etcd_io.raft.v3.FrameH

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

set_option hygiene false in
/-- The rest of `ApplyConfChange` once `AsV2` gave the `ConfChangeV2` `v2` (`#Hch`), in both
arms (`ConfChange`, `ConfChangeV2`): the payload by the mode, the send on `confc`, the receive
on `confstatec`. -/
local macro "apply_cc_send" : tactic => `(tactic| (
    ihave Hpay : iprop(|==> (confcP γ v2 ∗ (⌜γ.mode = .static⌝ ∨ (⌜γ.mode.isDyn = true⌝ ∗
        dghostVar γ.ccq (DFrac.own (1 : Qp).half) (k + 1, cs'))))) $$ [HR]
    · rcases Hmode with hm | ⟨dec, c0, h0, h1, hm⟩
      · imodintro
        isplitl []
        · unfold confcP
          iexists _
          iframe Hch
          ileft
          ipureintro
          exact ⟨hm, Hshr hm⟩
        ileft; ipureintro; exact hm
      · icases HR with (%Hs | ⟨Hcfg, #Hdlb⟩)
        · rw [hm] at Hs; cases Hs
        unfold nodeCfg
        icases Hcfg with ⟨Hcap, ⟨%x, Hq1, Hq2⟩, #Hcamlb⟩
        imod dghostVar_update_halves (k + 1, cs') γ.ccq x x $$ Hq1 Hq2 with ⟨Hq1, Hq2⟩
        imodintro
        isplitl [Hcap Hq1]
        · unfold confcP
          iexists _
          iframe Hch
          iright
          iexists ds, ca, cfg, k, e, cs'
          unfold dlvLb
          iframe Hdlb Hcap Hq1
          ipureintro
          refine ⟨by rw [hm]; rfl, fun dec' c0' h0' h1' hm' => ?_⟩
          exact Hdyn dec' c0' h0' h1' hm'
        iright
        iframe Hq2
        ipureintro; rw [hm]; rfl
    imod Hpay with ⟨HP, Hkeep⟩
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.confc', γ.confc, _
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hconfc
      iapply handshake_send_au γ.confc nv.confc' _ (confcP γ) iprop(True)
        $$ [$(frameH `Hlc1) $(frameH `Hlc2) $(frameH `Hlc3)] Hconfc HP
      inext
      iintro -
      wp_auto_lc 2
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
          nv.confstatec', γ.confstatec
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hconfstatec
        iapply handshake_receive_au γ.confstatec nv.confstatec' (confstateP γ) iprop(True) _
          $$ [$(frameH `Hlc1) $(frameH `Hlc2)] Hconfstatec []
        · itrivial
        inext
        iintro %csv Hcs
        wp_auto
        iunfold confstateP at Hcs
        icases Hcs with ⟨%csm, Hcs, (%Hs | ⟨%Hd, %w, Hcap, Hq, #Hlb, %Hok⟩)⟩
        · icases Hkeep with (%Hs' | ⟨%Hd', -⟩)
          · iapply HΦ $$ %csv %csm
            iframe Hcs
            ileft
            ipureintro; exact Hs
          · rw [Hs.1] at Hd'; cases Hd'
        · icases Hkeep with (%Hs' | ⟨%Hd', Hq'⟩)
          · rw [Hs'] at Hd; cases Hd
          ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hq Hq'
          subst Heq
          iapply HΦ $$ %csv %csm
          iframe Hcs
          iright
          isplitr
          · ipureintro; exact Hd
          isplitl
          rotate_left
          · ipureintro; exact Hok
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
        iapply handshake_false_recv_au γ.done nv.done' $$ [$(frameH `Hlc1) $(frameH `Hlc2)] Hdone
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
      iapply handshake_false_recv_au γ.done nv.done' $$ [$(frameH `Hlc1) $(frameH `Hlc2)] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial
  ))

/-- `cc.AsV2()` on `confc` (`confcP`, by the mode; the driver keeps the answer slot's other
half), then the `*ConfState` from `confstatec` (`confstateP`); `n.done` never fires. (Raft v3.7,
stage R5: `confc` carries `AsV2`'s pointer: a `ConfChange`'s fresh `ConfChangeV2`
(`m.asV2`), frozen (`ownCCV2_persist`), or a `ConfChangeV2` itself, read-only already; the
answer a `*pb.ConfState` owned, `csPts csp 1 cs true`.) -/
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
  · simp only [ownCCI]
    icases Hc with ⟨%p, %Hcv, Hc⟩
    subst Hcv
    wp_auto
    wp_apply +noauto wp_ConfChange_AsV2 p DFrac.discard m $$ [Hc] as %v2 ⟨-, Hch⟩
    · iexact Hc
    imod ownCCV2_persist $$ Hch with #Hch
    -- the payload, by the mode; the driver keeps the answer slot's other half
    apply_cc_send
  · simp only [ownCCI]
    icases Hc with ⟨%v2, %Hcv, #Hch⟩
    subst Hcv
    wp_auto
    wp_apply +noauto wp_ConfChangeV2_AsV2
    -- the payload, by the mode; the driver keeps the answer slot's other half
    apply_cc_send

end proof

end EtcdGrove
end Perennial
