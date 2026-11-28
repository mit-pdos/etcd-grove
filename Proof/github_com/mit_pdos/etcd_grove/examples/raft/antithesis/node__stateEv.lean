/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__stateEv.lean`: a fresh report
with the hard state's fields, the first index and the entries' reports (`Has = FTerm | FVote |
FCommit | FFirst | FEntries`: every other field absent).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__stateEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__entries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.firstIndex
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
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

theorem node.stateEv.wp_proof (wp_entries : node.entries.spec (GF := GF) (hG := hG))
    (wp_firstIndex : firstIndex.spec (GF := GF) (hG := hG)) (wp_Name : Name.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG)) :
    node.stateEv.spec (GF := GF) (hG := hG) := by
  intro c γ n j e hp hs sl dq els es hn
  wp_start as ⟨#Hc, #Hn, #Hhs, Hsl, #Hents⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetTerm.1 hp hs $$ [$Hpb $Hhs]
  try wp_auto
  wp_apply wp_GetVote.1 hp hs $$ [$Hpb $Hhs]
  try wp_auto
  wp_apply wp_Name hs.Vote' $$ [$Hpkg]
  try wp_auto
  wp_apply wp_GetCommit.1 hp hs $$ [$Hpb $Hhs]
  try wp_auto
  wp_apply wp_firstIndex sl dq els es $$ [$Hpkg $Hsl $Hents] as ⟨Hsl, -⟩
  try wp_auto
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, #Hro, -⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, -, -, -, #Hm, -⟩
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, -⟩
  wp_apply wp_entries c n γ.mode sl dq els es hn $$ [$Hpkg $Hnc $Hm $Hsl $Hents] as %out ⟨Hsl, -, #Hlog, Hr⟩
  try wp_auto
  iapply HΦ
  iframe Hsl Hents Hr
  iunfold eventOwn
  iexists _
  iframe
  simp only [stateEvM, AntCheck.fieldRO, AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.fieldRel]
  isplitr
  · ipureintro
    simp only [AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm,
      AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm,
      AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
    refine ⟨trivial, trivial, trivial, ?_⟩
    decide
  simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing, AntCheck.fMsg,
    AntCheck.fCause]
  iframe Hlog
  ipureintro; decide

/-- **`node.stateEv.specB2`** (#33 parity B2; staged beside B1's `wp_proof`): B1's proof over B2's
cluster and node records. -/
theorem node.stateEv.wp_proofB2 (wp_entries : node.entries.spec (GF := GF) (hG := hG))
    (wp_firstIndex : firstIndex.spec (GF := GF) (hG := hG)) (wp_Name : Name.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG)) :
    node.stateEv.specB2 (GF := GF) (hG := hG) := by
  intro c γ n j e hp hs sl dq els es hn
  wp_start as ⟨#Hc, #Hn, #Hhs, Hsl, #Hents⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetTerm.1 hp hs $$ [$Hpb $Hhs]
  try wp_auto
  wp_apply wp_GetVote.1 hp hs $$ [$Hpb $Hhs]
  try wp_auto
  wp_apply wp_Name hs.Vote' $$ [$Hpkg]
  try wp_auto
  wp_apply wp_GetCommit.1 hp hs $$ [$Hpb $Hhs]
  try wp_auto
  wp_apply wp_firstIndex sl dq els es $$ [$Hpkg $Hsl $Hents] as ⟨Hsl, -⟩
  try wp_auto
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, #Hro, -⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, -, -, -, #Hm, -⟩
  ihave #Hn' := Hn
  iunfold nodeROB2 at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, -⟩
  wp_apply wp_entries c n γ.mode sl dq els es hn $$ [$Hpkg $Hnc $Hm $Hsl $Hents] as %out ⟨Hsl, -, #Hlog, Hr⟩
  try wp_auto
  iapply HΦ
  iframe Hsl Hents Hr
  iunfold eventOwn
  iexists _
  iframe
  simp only [stateEvM, AntCheck.fieldRO, AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.fieldRel]
  isplitr
  · ipureintro
    simp only [AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm,
      AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm,
      AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
    refine ⟨trivial, trivial, trivial, ?_⟩
    decide
  simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing, AntCheck.fMsg,
    AntCheck.fCause]
  iframe Hlog
  ipureintro; decide

end proof

end AntHarness
end EtcdGrove
end Perennial
