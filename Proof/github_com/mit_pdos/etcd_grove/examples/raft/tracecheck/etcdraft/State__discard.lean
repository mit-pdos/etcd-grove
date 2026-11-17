/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__discard`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__discard
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Without

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem State.discard.wp_proof (wp_Without : Bag.Without.spec (GF := GF) (hG := hG)) :
    State.discard.spec (GF := GF) (hG := hG) := by
  intro p st M q m
  wp_start as ⟨Hst, #Hm, %Hnd⟩
  iunfold stateOwn at Hst
  icases Hst with ⟨%g, %sm, Hp, #Hsrv, HS, %Hkeys, %Hnd', Hsrvs, #Hb1, #Hb2, %Hrc⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Without_unfold.method_unfold]
  wp_auto
  wp_apply wp_Without _ _ _ _ $$ [Hb1 Hm] as %g' #Hg'
  · iframe Hb1 Hm; ipureintro; exact Hnd
  wp_auto
  iapply HΦ
  iunfold stateOwn
  iexists { g with Messages' := g' }, sm
  isplitl [Server S Messages PendingMessages ReconfigCount PreVote CheckQuorum]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  simp only [State.discard]
  iframe Hsrv HS Hsrvs Hb2 Hg'
  ipureintro; exact ⟨Hkeys, Hnd', Hrc⟩

end proof

end Etcdraft
end EtcdGrove
end Perennial
