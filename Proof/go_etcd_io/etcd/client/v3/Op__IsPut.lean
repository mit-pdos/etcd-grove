/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__IsPut.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__IsPut

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Op.IsPut.wp_proof : Op.IsPut.spec (GF := GF) (hG := hG) := by
  intro opp op o dq
  simp only [opFullAt]
  wp_start as ⟨Hop, ⟨Hat, #Hkey, %Hf, #Hval, #Hsort⟩⟩
  obtain ⟨Ht, Hko, -, -, -, -, -, -⟩ := Hf
  wp_auto
  wp_method_call
  wp_auto
  rw [Ht]
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
