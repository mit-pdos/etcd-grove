/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__ExpiredLeasesC.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__ExpiredLeasesC

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.ExpiredLeasesC.wp_proof :
    lease.lessor.ExpiredLeasesC.spec (GF := GF) (hG := hG) := by
  intro lp
  wp_start as #Hc
  iunfold lessorExpiredC at Hc
  icases Hc with ⟨%c, %γc, #Hcf, #Hbag⟩
  (try wp_auto)
  iapply HΦ
  iexists γc; iexact Hbag

end proof

end EtcdGrove
end Perennial
