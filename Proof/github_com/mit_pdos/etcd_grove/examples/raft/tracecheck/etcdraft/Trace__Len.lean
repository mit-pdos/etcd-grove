/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__Len`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__Len

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

theorem Trace.Len.wp_proof : Trace.Len.spec (GF := GF) (hG := hG) := by
  intro t tr
  wp_start as #Ht
  iunfold traceRO at Ht
  icases Ht with ⟨%Hv, %g, #Hp, ⟨%lns, #Hlns, #Hl⟩, -⟩
  ihave %Hlen := ownSlice_len $$ Hlns
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hl
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  iapply HΦ; ipureintro
  unfold Trace.len; rw [← Hl2, Hlen.1]; word

end proof

end Etcdraft
end EtcdGrove
end Perennial
