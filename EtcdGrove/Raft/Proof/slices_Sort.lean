/-
`slices.Sort` on `[]uint64`: Perennial's `slices.wp_Sort_uint64`.
-/
import EtcdGrove.Raft.Spec.slices_Sort
import Perennial.Proof.slices_proof.sort

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
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
