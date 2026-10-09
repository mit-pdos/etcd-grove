/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Cmp__ensureCompare.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Cmp__ensureCompare

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Cmp.ensureCompare.wp_proof : Cmp.ensureCompare.spec (GF := GF) (hG := hG) := by
  intro cmpp c
  wp_start as ⟨Hc, %Hnn⟩
  wp_auto
  simp only [Hnn, decide_false]
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
