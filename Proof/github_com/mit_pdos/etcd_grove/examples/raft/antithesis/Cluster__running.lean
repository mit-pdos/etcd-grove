/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__running.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__running
public import Perennial.Spec.time.Sleep
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
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Cluster.running.wp_proof (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    Cluster.running.spec (GF := GF) (hG := hG) := by
  intro c γ d
  wp_start as #Hc
  iunfold antCluster at Hc
  icases Hc with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  wp_auto
  wp_apply wp_Sleep
  try wp_auto
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)] iprop((∀ b : Bool, True -∗ Φ #b) ∗ «$res0_ptr» ↦ false)
      $$ [] [HΦ «$res0»] []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro ⟨HΦ, Hres⟩
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stop, γ.stopCh
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hbc
    iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ _ $$ Hbc
    isplit
    · iintro -
      try wp_auto
      iapply HΦ
      itrivial
    · iintro -
      iframe
  · iframe
  · iintro ⟨HΦ, Hres⟩ -
    try wp_auto
    iapply HΦ
    itrivial

end proof

end AntHarness
end EtcdGrove
end Perennial
