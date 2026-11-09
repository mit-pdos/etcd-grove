/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Set__Add`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Add
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Union

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

theorem Set.Add.wp_proof (wp_Union : Set.Union.spec (GF := GF) (hG := hG)) :
    Set.Add.spec (GF := GF) (hG := hG) := by
  intro sl s id
  wp_start as #Hs
  iapply wp_fupd
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, -⟩
  imod ownSlice_persist $$ Hsl0 with #Hsl0
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Union_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Union sl s _ [uint.nat id] $$ [Hsl0] as %u #Hu
  · iframe Hs
    iunfold setRO
    iexists [id]
    iframe Hsl0
    ipureintro; rfl
  try wp_auto
  imodintro
  iapply HΦ
  unfold SetIds.add
  iexact Hu

end proof

end Etcdraft
end EtcdGrove
end Perennial
