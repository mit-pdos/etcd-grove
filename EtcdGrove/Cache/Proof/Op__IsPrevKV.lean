/-
Proof of `Spec/Op__IsPrevKV.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.Op__IsPrevKV

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

theorem Op.IsPrevKV.wp_proof : Op.IsPrevKV.spec (GF := GF) (hG := hG) := by
  intro opp op o dq
  simp only [opAt]
  wp_start as ⟨Hop, ⟨%Hf, -⟩⟩
  wp_auto
  wp_method_call
  wp_auto
  rw [Hf.2.1]
  wp_end

end proof

end EtcdGrove
end Perennial
