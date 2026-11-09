/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__IgnoreInLease`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__IgnoreInLease

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

theorem State.IgnoreInLease.wp_proof : State.IgnoreInLease.spec (GF := GF) (hG := hG) := by
  intro p st q m
  wp_start as ⟨#Hst, #Hmsg, %Hcq⟩
  have hnone : st.ignoreInLease m = none := by
    unfold State.ignoreInLease; simp [Hcq]
  rw [hnone]
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%g, %sm, #Hp, #Hsrv, #Hm, %Hkeys, %Hnd, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨#P1, #P2, #P3, #P4, #P5, #P6, #P7, -⟩
  read_msg
  wp_auto
  wp_apply wp_map_lookup2 $$ [Hm] as -
  · iexact Hm
  cases hk : (sm !! gm.Dest').isSome
  · wp_auto
    iapply HΦ; ipureintro; rfl
  wp_auto
  rw [Hrc.2.2, Hcq]
  wp_auto
  iapply HΦ; ipureintro; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
