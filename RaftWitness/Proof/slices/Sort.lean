/-
`slices.Sort` on `[]uint64`: Perennial's `slices.wp_Sort_uint64`.
-/
module

public import RaftWitness.Spec.slices.Sort
public import Perennial.Proof.slices

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem slices.«Sort».wp_proof : slices.«Sort».spec (GF := GF) (hG := hG) := by
  intro data xs
  wp_start_folded as ⟨Hxs, %Hlen⟩
  wp_apply _root_.Perennial.slices.wp_Sort_uint64 data xs $$ [$Hxs] as %xs' ⟨Hxs, %Hperm, %Hsorted⟩
  · ipureintro; exact Hlen
  iapply HΦ
  iframe
  ipureintro
  exact ⟨Hperm, Hsorted⟩

end proof

end EtcdGrove
end Perennial
