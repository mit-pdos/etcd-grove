/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__send`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__send
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__With

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

theorem State.send.wp_proof (wp_With : Bag.With.spec (GF := GF) (hG := hG)) :
    State.send.spec (GF := GF) (hG := hG) := by
  intro p st M q m
  wp_start as ⟨Hst, #Hm, %Hnd, %Hc⟩
  iunfold stateOwn at Hst
  icases Hst with ⟨%g, %sm, Hp, #Hsrv, HS, %Hkeys, %Hnd', Hsrvs, #Hb1, #Hb2, %Hrc⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_With_unfold.method_unfold]
  wp_auto
  wp_apply wp_With _ _ _ _ $$ [Hb2 Hm] as %g' #Hg'
  · iframe Hb2 Hm; ipureintro; exact ⟨Hnd, Hc⟩
  wp_auto
  iapply HΦ
  iunfold stateOwn
  iexists { g with PendingMessages' := g' }, sm
  isplitl [Server S Messages PendingMessages ReconfigCount PreVote CheckQuorum]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  simp only [State.send]
  iframe Hsrv HS Hsrvs Hb1 Hg'
  ipureintro; exact ⟨Hkeys, Hnd', Hrc⟩

end proof

end Etcdraft
end EtcdGrove
end Perennial
