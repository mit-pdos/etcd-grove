/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__MessageTermsLtCurrentTerm`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__MessageTermsLtCurrentTerm
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StateRead

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

theorem State.MessageTermsLtCurrentTerm.wp_proof :
    State.MessageTermsLtCurrentTerm.spec (GF := GF) (hG := hG) := by
  intro p st q m
  wp_start as ⟨#Hst, #Hmsg⟩
  iunfold stateRO at Hst
  icases Hst with ⟨%g, %sm, #Hp, #Hsrv, #HS, %Hkeys, %Hnd, #Hsrvs, #Hm, #Hpm, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  iunfold msgRO at Hmsg
  icases Hmsg with ⟨%gm, #Hq, %Hmf, -⟩
  icases typedPointsto_split _ _ _ $$ Hq with Hqf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hqf
  wp_auto
  wp_apply wp_map_lookup2 $$ [HS] as -
  · iexact HS
  have hsrc : m.source = uint.nat gm.Source' := Hmf.2.2.2.2.2.2.2.2.2.2.2.1.symm
  by_cases hin : uint.nat gm.Source' ∈ st.server
  · icases servers_at st sm gm.Source' hin $$ Hsrvs with ⟨%qv, %Hqv, #Hv⟩
    iunfold serverRO at Hv
    icases Hv with ⟨%gv, %mv, #Hqv', %Hfv, -, -, -, -, -, -, -⟩
    icases typedPointsto_split _ _ _ $$ Hqv' with Hqvf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hqvf
    rw [Hqv]
    simp only [Option.getD_some, Option.isSome_some, decide_true]
    wp_auto
    have : st.messageTermsLtCurrentTerm m = decide (sint.Z gm.Term' ≤ sint.Z gv.CurrentTerm') := by
      unfold State.messageTermsLtCurrentTerm
      rw [hsrc, Hmf.2.2.1, ← Hfv.1]
      simp [hin]
    rw [← this]
    iapply HΦ
    ipureintro; trivial
  · have hnone : sm !! gm.Source' = none := by
      cases h : sm !! gm.Source' with
      | none => rfl
      | some _ => exact absurd ((Hkeys _).1 (by rw [h]; rfl)) hin
    rw [hnone]
    simp only [Option.getD_none, Option.isSome_none]
    wp_auto
    have : st.messageTermsLtCurrentTerm m = false := by
      unfold State.messageTermsLtCurrentTerm
      rw [hsrc]
      simp [hin]
    rw [← this]
    iapply HΦ
    ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
