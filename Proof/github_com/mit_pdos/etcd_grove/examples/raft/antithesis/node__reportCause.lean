/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__reportCause.lean`: with a
pending cause, its message is copied into a fresh `recv` report (`Has = FMsg`: every other field
absent), the cell cleared, and the report emitted.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__reportCause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit

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

theorem node.reportCause.wp_proof (wp_emit : node.emit.spec (GF := GF) (hG := hG)) :
    node.reportCause.spec (GF := GF) (hG := hG) := by
  intro c γ n j cl o Q
  cases o with
  | none =>
    simp only [Option.toList, List.map_nil, reports]
    wp_start as ⟨#Hc, #Hn, Hok, Hcl, Hpc, Hrep⟩
    iunfold pendingCause at Hpc
    icases Hpc with (⟨%Hnil, -⟩ | ⟨%g, %m, ⟨-, %Ho⟩, -, -⟩)
    · subst Hnil
      wp_auto
      iapply HΦ
      iframe
    · cases Ho
  | some ev =>
    simp only [Option.toList, List.map_cons, List.map_nil]
    wp_start as ⟨#Hc, #Hn, Hok, Hcl, Hpc, Hrep⟩
    iunfold pendingCause at Hpc
    icases Hpc with (⟨-, %Ho⟩ | ⟨%g, %m, ⟨%Hnn, %Ho⟩, Hg, #Hm⟩)
    · cases Ho
    cases Ho
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply wp_emit c γ n j _ (recvEvM m) Q $$ [$Hpkg $Hc $Hn $Hok Hrep «$a0»] as ⟨Hok, HQ⟩
    · iframe Hrep
      iunfold eventOwn
      iexists _
      iframe
      simp only [recvEvM, AntCheck.fieldRO, AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.fieldRel]
      isplitr
      · ipureintro
        refine ⟨trivial, trivial, trivial, ?_⟩
        simp only [AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm,
          AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm,
          AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
        decide
      simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing, AntCheck.fMsg,
        AntCheck.fCause]
      iframe Hm
      ipureintro; decide
    try wp_auto
    iapply HΦ
    iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
