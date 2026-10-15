/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/isPriorityRequest.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.isPriorityRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem isPriorityRequest.wp_proof : isPriorityRequest.spec (GF := GF) (hG := hG) := by
  intro p rq
  wp_start as #Hirr
  ihave #Hirr' := Hirr
  iunfold irrNoHdrIs at Hirr'
  icases Hirr' with ⟨%Hpn, -, -, -, -, -, -, -, ⟨%l, #Hl, #Hlr⟩, -⟩
  ihave %Hlr' := apply.optReqIs_nil l rq.leaseRevoke _ apply.leaseRevokeIs_nn $$ Hlr
  wp_auto
  wp_if_destruct
  · exact absurd (by simpa using Hif) Hpn
  · have hb : (!decide (l = null)) = rq.leaseRevoke.isSome := by
      cases h : rq.leaseRevoke with
      | none => simp [Hlr'.2 h]
      | some _ =>
        have hl : l ≠ null := fun e => by rw [Hlr'.1 e] at h; cases h
        simp [hl]
    rw [hb]
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
