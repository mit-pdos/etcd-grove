/-
The proof of `rpctransport.Transport.AppendEntriesPipeline` (ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/inproc, 241f27e).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__AppendEntriesPipeline
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline__run
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline__AppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline__Consumer
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline__Close

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
theorem isPip_isPipeline
    (wp_pAppendEntries : github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.AppendEntries.spec (GF := GF) (hG := hG))
    (wp_pConsumer : github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.Consumer.spec (GF := GF) (hG := hG))
    (wp_pClose : github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.Close.spec (GF := GF) (hG := hG))
    (p : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (j : github_com.hashicorp.raft.proto.SID) (T : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isPip p γ j T ⊢
      github_com.hashicorp.raft.isPipeline (interface.mk (go.GoType.PointerType pipeline.ty) #p) γ j T := by
  iintro ⟨#Hpkg, #Hp⟩
  unfold github_com.hashicorp.raft.isPipeline
  isplitr
  · imodintro
    iintro %args %resp %rq %rp0 %snd %prev %pt %ents %lci %ss %Φ #Hargs Hrq Hrp %Hrp0 HΦ
    iapply wp_pAppendEntries p γ j T args resp rq rp0 snd prev pt ents lci ss
      $$ [$Hpkg $Hp $Hargs $Hrq $Hrp]
    · ipureintro; exact Hrp0
    inext; iintro %fi %err Herr; iapply HΦ $$ Herr
  isplitr
  · imodintro
    iintro %Φ HΦ
    iapply wp_pConsumer p γ j T $$ [$Hpkg $Hp]
    inext; iintro %ch Hch; iapply HΦ $$ Hch
  · imodintro
    iintro %Φ HΦ
    iapply wp_pClose p γ j T $$ [$Hpkg $Hp]
    inext; iintro -; iexact HΦ

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.AppendEntriesPipeline.wp_proof
    (wp_run : github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.run.spec (GF := GF) (hG := hG))
    (wp_pAppendEntries : github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.AppendEntries.spec (GF := GF) (hG := hG))
    (wp_pConsumer : github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.Consumer.spec (GF := GF) (hG := hG))
    (wp_pClose : github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.Close.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.AppendEntriesPipeline.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C id j T
  wp_start as #Ht
  wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 128)) as %qch %γq ⟨#Hqc, %Hqcap, Hqown⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 128)) as %cch %γc ⟨#Hcc, %Hccap, Hcown⟩
  · ipureintro; decide
  wp_apply (chan.wp_make1 (V := Unit)) as %cc %γcl ⟨#Hccc, -, Hccown⟩
  irename «$r0» => Hpp
  iStructNamed Hpp
  imod start_bag (futQ γ T) _ qch γq (by simp) $$ Hqc Hqown with #Hqb
  imod start_bag (github_com.hashicorp.raft.pipeFut γ j T) _ cch γc (by simp) $$ Hcc Hcown with #Hcb
  imod alloc_broadcast_chan iprop(True) γcl cc $$ Hccc Hccown with Hcl
  icases ownBroadcastChan_open _ _ _ _ $$ Hcl with ⟨%γch, #Hcli, Hclh⟩
  ihave Hclp := ownBroadcastChan_close cc γcl iprop(True) .Pending γch $$ [$Hcli $Hclh]
  ihave #Hclu := ownBroadcastChan_close cc γcl iprop(True) .Unknown γch $$ [$Hcli]
  imod sync.init_Mutex (pipLocked «$r0_ptr» cc γcl) ⊤ _ $$ mu [closed Hclp] with #Hlock
  · inext
    unfold pipLocked
    iexists false
    iframe
  ipersist t
  ipersist target
  ipersist queue
  ipersist consumer
  ipersist closeCh
  ihave #Hpip : isPip «$r0_ptr» γ j T $$ []
  · unfold isPip
    iexists _, snapP, i, W, C, qch, cch, cc, γq, γc, γcl
    iframe t target queue consumer closeCh Ht Hqb Hcb Hlock Hclu
  wp_bind (Fork _)
  iapply wp_fork
  · inext
    iapply wp_run «$r0_ptr» γ j T $$ [$Hpkg $Hpip]
    inext
    iintro -
    ipureintro; exact isPanic_intoVal ()
  inext
  wp_auto
  wp_end
  isplitr
  · ipureintro; rfl
  iexists (interface.mk (go.GoType.PointerType pipeline.ty) #«$r0_ptr»)
  isplitr
  · ipureintro; rfl
  iapply isPip_isPipeline wp_pAppendEntries wp_pConsumer wp_pClose «$r0_ptr» γ j T $$ [$Hpkg $Hpip]


end proof

end Perennial
