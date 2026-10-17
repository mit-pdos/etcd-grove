/-
Proof of `Spec/isCreateEvent.lean` (etcd-io/etcd#21600). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.isCreateEvent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem isCreateEvent.wp_proof : isCreateEvent.spec (GF := GF) (hG := hG) := by
  intro ev e cr
  wp_start as ⟨#Hev, #Hcr⟩
  simp only [eventAt]
  icases Hev with ⟨%keySl, #Htyp, #Hkv, #Hkey, #Hks, #Hmod⟩
  iunfold eventCreateRevAt at Hcr
  wp_auto
  wp_if_destruct
  · have h : decide (cr = e.rev) = isCreateModel e cr := by
      simp_all [isCreateModel]
    rw [h]
    iapply HΦ
    itrivial
  · have h : false = isCreateModel e cr := by
      simp_all [isCreateModel]
    rw [h]
    iapply HΦ
    itrivial
end proof

end EtcdGrove
end Perennial
