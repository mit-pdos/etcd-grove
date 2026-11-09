/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__Len`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Len

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

theorem Bag.Len.wp_proof : Bag.Len.spec (GF := GF) (hG := hG) := by
  intro g b
  wp_start as #Hg
  iunfold bagRO at Hg
  icases Hg with ⟨%items, #Hits, #Hib⟩
  ihave %Hil := ownSlice_len $$ Hits
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hib
  wp_auto
  iapply HΦ; ipureintro
  rw [← Hbl, Hil.1]; word

end proof

end Etcdraft
end EtcdGrove
end Perennial
