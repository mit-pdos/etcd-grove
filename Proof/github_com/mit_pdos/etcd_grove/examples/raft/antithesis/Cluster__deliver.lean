/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__deliver.lean`: the `select`'s
send case puts the input in node `j`'s bag (its `inputOk` the bag's predicate), the receive case on
the stop channel (a broadcast) drops it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__deliver
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Cluster.deliver.wp_proof : Cluster.deliver.spec (GF := GF) (hG := hG) := by
  intro c γ n j inp
  wp_start as ⟨#Hc, #Hn, Hinp⟩
  iunfold antCluster at Hc
  icases Hc with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  iunfold nodeRO at Hn
  icases Hn with ⟨%ch, %d, #Hnc, #Hid, #Hname, #Hin, #Hbag, #Hd, #Hlog⟩
  ihave #Hsch := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists H.input, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ.inCh j, inp
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_send_au $$ [$Hlc1 $Hlc2] Hbag Hinp
    inext
    (try wp_auto)
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stop, γ.stopCh
    isplit
    · ipureintro; rfl
    isplit
    · iexact Hsch
    iapply broadcast_chan_receive $$ Hbc
    iintro -
    (try wp_auto)
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end AntHarness
end EtcdGrove
end Perennial
