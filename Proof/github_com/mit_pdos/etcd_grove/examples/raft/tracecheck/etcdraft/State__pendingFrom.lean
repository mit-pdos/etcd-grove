/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__pendingFrom`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__pendingFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Filter

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

theorem State.pendingFrom.wp_proof (wp_Filter : Bag.Filter.spec (GF := GF) (hG := hG)) :
    State.pendingFrom.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as #Hst
  iunfold stateRO at Hst
  icases Hst with ⟨%g, %sm, #Hp, #Hsrv, #HS, %Hkeys, %Hnd, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  ipersist i
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Filter_unfold.method_unfold]
  wp_auto
  wp_apply wp_Filter _ _ _ (fun m => m.source == (uint.nat i : ID)) $$ [Hb2] as %g' #Hg'
  · iframe Hb2
    imodintro
    iintro %q %m
    wp_start as #Hm
    iunfold msgRO at Hm
    icases Hm with ⟨%v, #Hq, %Hv, #Hve⟩
    icases typedPointsto_split _ _ _ $$ Hq with Hqf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hqf
    wp_auto
    have hs := uint_eq_iff v.Source' i _ (uint.nat i) Hv.2.2.2.2.2.2.2.2.2.2.2.1 rfl
    have : decide (v.Source' = i) = (m.source == uint.nat i) := by
      by_cases h : m.source = uint.nat i
      · rw [decide_eq_true (hs.2 h)]; simp [h]
      · rw [decide_eq_false (fun x => h (hs.1 x))]; simp [h]
    rw [this]
    iapply HΦ; ipureintro; trivial
  try wp_auto
  iapply HΦ
  unfold State.pendingFrom
  iexact Hg'

end proof

end Etcdraft
end EtcdGrove
end Perennial
