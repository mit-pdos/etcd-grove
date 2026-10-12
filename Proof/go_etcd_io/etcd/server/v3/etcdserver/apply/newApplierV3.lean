/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Backend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newQuotaApplierV3
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newAuthApplierV3

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.newApplierV3.wp_proof
    (hB : apply.newApplierV3Backend.spec (GF := GF) (hG := hG))
    (hQ : apply.newQuotaApplierV3.spec (GF := GF) (hG := hG))
    (hA : apply.newAuthApplierV3.spec (GF := GF) (hG := hG)) :
    apply.newApplierV3.spec (GF := GF) (hG := hG) := by
  intro E opts
  wp_start as #Hopts
  ihave #Hok := Hopts
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨-, -, -, #Hle, #Has, -⟩
  wp_auto
  wp_apply (hB E opts) $$ [] as %b #Hb
  · iframe #
  wp_apply (hQ E .backend opts.Logger' opts.QuotaBackendBytesCfg' opts.Backend' b) $$ [] as %q #Hq
  · iframe #
  wp_apply (hA E (.quota .backend) opts.AuthStore' q opts.Lessor') $$ [] as %p #Hp
  · iframe #
  iapply HΦ
  simp only [apply.baseChain]
  iexact Hp

end proof

end EtcdGrove
end Perennial
