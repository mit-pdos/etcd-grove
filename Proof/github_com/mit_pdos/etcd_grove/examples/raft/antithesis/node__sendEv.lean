/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__sendEv.lean`: a fresh `send`
report (`Has = FBy | FMsg`: every other field absent) of the message's report (`node.msg`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sendEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__msg
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.SpecsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReportB2

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

theorem node.sendEv.wp_proof (wp_msg : node.msg.spec (GF := GF) (hG := hG)) :
    node.sendEv.spec (GF := GF) (hG := hG) := by
  intro c γ n j by_ ml dq dqe cap st hns hn
  wp_start as ⟨#Hc, #Hn, Hm⟩
  wp_auto
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, #Hro, -⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, -, -, -, #Hmd, -⟩
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, -⟩
  wp_apply wp_msg c n γ.mode ml dq dqe cap st hns hn $$ [$Hpkg $Hnc $Hmd $Hm] as %g ⟨Hm, #Hg, Hr⟩
  try wp_auto
  iapply HΦ
  iframe Hm Hr
  iunfold eventOwn
  iexists _
  iframe
  simp only [sendEvM, AntCheck.fieldRO, AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.fieldRel]
  isplitr
  · ipureintro
    refine ⟨trivial, trivial, trivial, ?_⟩
    simp only [AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm,
      AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm,
      AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
    decide
  simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing, AntCheck.fMsg,
    AntCheck.fCause]
  iframe Hg
  ipureintro; decide

/-- **`node.sendEv.specB2`** (#33 parity B2; staged beside B1's `wp_proof`): B1's proof over B2's
cluster and node records. -/
theorem node.sendEv.wp_proofB2 (wp_msg : node.msg.spec (GF := GF) (hG := hG)) :
    node.sendEv.specB2 (GF := GF) (hG := hG) := by
  intro c γ n j by_ ml dq dqe cap st hns hn
  wp_start as ⟨#Hc, #Hn, Hm⟩
  wp_auto
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, #Hro, -⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, -, -, -, #Hmd, -⟩
  ihave #Hn' := Hn
  iunfold nodeROB2 at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, -⟩
  wp_apply wp_msg c n γ.mode ml dq dqe cap st hns hn $$ [$Hpkg $Hnc $Hmd $Hm] as %g ⟨Hm, #Hg, Hr⟩
  try wp_auto
  iapply HΦ
  iframe Hm Hr
  iunfold eventOwn
  iexists _
  iframe
  simp only [sendEvM, AntCheck.fieldRO, AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.fieldRel]
  isplitr
  · ipureintro
    refine ⟨trivial, trivial, trivial, ?_⟩
    simp only [AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm,
      AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm,
      AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
    decide
  simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing, AntCheck.fMsg,
    AntCheck.fCause]
  iframe Hg
  ipureintro; decide

end proof

end AntHarness
end EtcdGrove
end Perennial
