/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__input.lean`: without batching,
`input` is the drain (`node.drain`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__input
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__drain
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

theorem node.input.wp_proof (wp_drain : node.drain.spec (GF := GF) (hG := hG)) :
    node.input.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v net₀ xnet₀ r₁ xs₁ q sl
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, %Hb1⟩
  have Hbatch : γ.mode.Batch' = false := Hb1.1
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, #Hns, #Hnsl, %HN, #Hmd, #Hiv, #Hivs⟩
  ihave Hmd' := Hmd
  iStructNamed Hmd'
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, #Hid, #Hname, #Hin, #Hbag, #Hd, #Hlog⟩
  wp_auto
  rw [Hbatch]
  wp_auto
  wp_apply wp_drain c γ n j v net₀ xnet₀ r₁ xs₁ q $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as
    %v' ⟨Hown, Had, Htok, %Hby⟩
  · ipureintro; exact Hb1
  try wp_auto
  iapply HΦ
  iframe Hown Had Htok
  ipureintro; exact Hby

end proof

end AntHarness
end EtcdGrove
end Perennial
