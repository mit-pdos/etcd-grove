/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Advance
public import Proof.go_etcd_io.raft.v3.InvAdvance
import all Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode

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

/-- The `dlv` halves move on past the `Ready` (`run` will recognize its record), one goes
with the receipt on `advancec`; `n.done` never fires. -/
theorem node.Advance.wp_proof : node.Advance.spec (GF := GF) (hG := hG) := by
  intro γ id n ds es ca cfg p' L HA1
  wp_start as ⟨Hbusy, Hrcpt, Hcfg⟩
  unfold nodeDriverBusy
  icases Hbusy with ⟨#Hnode, #Hdlb, %d, %ce, %p, Hd1, Hd2, Hrof, %Hds, %q0, Hr1, Hr2⟩
  ihave #Hcamlb : monoNatLbOwn γ.cam ca $$ [Hcfg]
  · unfold nodeCfg; icases Hcfg with ⟨-, -, $⟩
  subst Hds
  ihave #Hnode' := Hnode
  open_node Hnode'
  imod dghostVar_update_halves (dlvAfter d ce L, p') γ.dlv (d, p) (d, p) $$ Hd1 Hd2 with ⟨Hd1, Hd2⟩
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `advancec <- struct{}{}` (D19i part 1: `advInv`, the floor raised at the rendezvous)
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.advancec',
      γ.advancec, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isAdvChan_isChan $$ Hadvancec
    iapply adv_send_au γ nv.rn' id nv.advancec' (dlvAfter d ce L) L q0
      $$ [$Hlc1 $Hlc2 $Hlc3] Hadvancec [Hd1 Hrof Hrcpt] Hdlb Hr1 Hr2
    · unfold advanceP
      iexists d, ce, es, p'
      iframe Hd1 Hrof Hrcpt
      iexists ca
      iframe Hcamlb
      ipureintro; exact HA1
    inext
    iintro Hfl Hreq
    wp_auto
    iapply HΦ
    iframe Hcfg Hfl
    unfold nodeDriver
    iframe Hnode Hd2 Hdlb Hreq
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-n.done`: never
    simp only [chan.blockingClausePre]
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
