/-
Proof of `Spec/Op__MaxCreateRev.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__MaxCreateRev

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Op.MaxCreateRev.wp_proof : Op.MaxCreateRev.spec (GF := GF) (hG := hG) := by
  intro opp op o dq
  simp only [opAt]
  wp_start as ⟨Hop, ⟨%Hf, -⟩⟩
  wp_auto
  wp_method_call
  wp_auto
  rw [Hf.2.2.2.2.2.2.2.1]
  wp_end

end proof

end EtcdGrove
end Perennial
