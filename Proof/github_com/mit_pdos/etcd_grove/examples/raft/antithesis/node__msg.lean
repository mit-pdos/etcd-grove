/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__msg.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__msg
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.msgOf
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
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

variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.msg.wp_proof (wp_msgOf : msgOf.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    node.msg.spec (GF := GF) (hG := hG) := by
  intro c γ n j ml dq dqe cap st hsnap hnorm
  wp_start as ⟨#Hc, #Hn, Hml⟩
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
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetTo.1 ml _ _ _ st $$ [$Hpb $Hml] as Hml
  try wp_auto
  wp_apply wp_msgOf ml dq dqe cap st st.msg.To' γ.mode.Nodes' hsnap hnorm $$ [$Hpkg $Hml] as %g ⟨Hml, #Hg, Hr⟩
  try wp_auto
  iapply HΦ
  iframe
  iexact Hg

end proof

end AntHarness
end EtcdGrove
end Perennial
