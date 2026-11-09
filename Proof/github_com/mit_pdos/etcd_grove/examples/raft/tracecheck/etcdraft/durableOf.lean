/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `durableOf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.durableOf

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

theorem durableOf.wp_proof : durableOf.spec (GF := GF) (hG := hG) := by
  intro p dq g v
  wp_start as ⟨Hp, %Hf, #Hl, #Hc⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  ihave Hp : p ↦{dq} g $$ [-HΦ]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe Hp
  iunfold durableRO
  isplitr
  · ipureintro; exact Hf
  simp only [durableOf]
  iframe Hl Hc

end proof

end Etcdraft
end EtcdGrove
end Perennial
