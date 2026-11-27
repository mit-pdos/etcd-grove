/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__entries.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__entries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entriesOf
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

theorem node.entries.wp_proof (wp_entriesOf : entriesOf.spec (GF := GF) (hG := hG)) :
    node.entries.spec (GF := GF) (hG := hG) := by
  intro c γ n j sl dq els es hnorm
  wp_start as ⟨#Hc, #Hn, Hsl, #Hents⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, #Hid, #Hname, #Hin, #Hbag, #Hd, #Hlog⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, #Hns, #Hnsl, %HN, #Hm, #Hiv, #Hivs⟩
  ihave Hm' := Hm
  iStructNamed Hm'
  wp_auto
  wp_apply wp_entriesOf sl dq els es γ.mode.Nodes' hnorm $$ [$Hpkg $Hsl $Hents] as %out ⟨Hsl, #Hout, Hr⟩
  try wp_auto
  iapply HΦ
  iframe
  iframe Hents Hout

end proof

end AntHarness
end EtcdGrove
end Perennial
