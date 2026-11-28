/-
The proof of `rpctransport.New`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.New
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.NewConn
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

set_option goose.wp.extras true



theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.New.wp_proof
    (wp_NewConn : github_com.hashicorp.raft.examples.hraftnet.rpctransport.NewConn.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.New.spec (GF := GF) (hG := hG) := by
  intro lc peers dq M d γ snapP W C
  wp_start as ⟨Hpm, #HM, %Hrb, #Hcodec, %Hlaws⟩
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) github_com.hashicorp.raft.ServerAddress.ty
    (go.GoType.PointerType Conn.ty)) as %cm Hcm
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoString)
    (fun _ _ => iprop(∃ (Mc : GMap GoString Loc) (k0 v0 : GoString), conns_ptr ↦ cm ∗ cm ↦$ Mc ∗
      a_ptr ↦ k0 ∗ addr_ptr ↦ v0 ∗ [∗map] a ↦ p ∈ Mc, peerOk γ snapP W a p))
    _ _ _ peers M dq) $$ Hpm
  iintro %keys %Hkeys
  isplitl [conns Hcm a addr]
  · iexists ∅, _, _
    iframe
    iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2
    iempintro
  isplitr
  · imodintro
    iintro %idx %key %v ⟨%hk, %hv⟩ ⟨%Mc, %k0, %v0, conns, Hcm, a, addr, HMc⟩
    wp_auto
    ihave #Hv := (BigSepM.bigSepM_lookup (Φ := fun a na => iprop(net.rpc.rpcAddr (Gg := hG.goose_globalGS) W na ∗
      svcAt γ snapP W a na)) (show get? M key = some v from hv)) $$ HM
    icases Hv with ⟨#Hra, #HS⟩
    wp_apply wp_NewConn W v $$ [$Hra] as %p #Hp
    · ipureintro; exact Hrb
    wp_apply (wp_mapInsert github_com.hashicorp.raft.ServerAddress.ty cm Mc key p) $$ [$Hcm] as Hcm
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    iexists _, key, v
    iframe conns Hcm a addr
    ihave #Hpk : peerOk γ snapP W key p $$ []
    · unfold peerOk; iexists v; iframe Hp; iexact HS
    cases hMc : Mc !! key with
    | none =>
      iapply (BigSepM.bigSepM_insert (show get? Mc key = none from hMc)).2
      iframe Hpk HMc
    | some x =>
      icases (BigSepM.bigSepM_insert_acc (show get? Mc key = some x from hMc)) $$ HMc with ⟨-, Hacc⟩
      iapply Hacc $$ Hpk
  iintro ⟨%Mc, %k0, %v0, conns, Hcm, a, addr, HMc⟩ Hpm
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make1 (V := github_com.hashicorp.raft.RPC)) as %ch %γc ⟨#Hch, -, Hoc⟩
  imod start_bag (github_com.hashicorp.raft.rpcP γ snapP lc) _ ch γc (by simp) $$ Hch Hoc with #Hbag
  (try wp_auto)
  irename «$r0» => Ht
  iStructNamed Ht
  ipersist «local'»
  ipersist timeout
  ipersist consumer
  ipersist peers
  ipersist Hcm
  imod sync.init_Mutex (hbInv γ lc «$r0_ptr») ⊤ _ $$ mu [hb] with #Hmu
  · inext
    unfold hbInv
    iexists _
    iframe hb
    ileft; ipureintro; rfl
  ihave #Hrpc : github_com.hashicorp.raft.isRpcChan γ snapP lc ch $$ []
  · unfold github_com.hashicorp.raft.isRpcChan; iexists γc; iexact Hbag
  imodintro
  iapply HΦ
  iframe Hpm
  unfold isTrans
  iexists d, ch, cm, Mc
  simp only [named]
  iframe HMc «local'» timeout consumer Hrpc peers Hcm Hmu Hcodec
  ipureintro; exact Hlaws

end proof

end Perennial
