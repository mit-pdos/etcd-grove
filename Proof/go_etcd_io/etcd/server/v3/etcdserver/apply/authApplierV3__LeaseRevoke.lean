/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.authApplierV3.LeaseRevoke.wp_proof
    (hLP : apply.checkLeasePuts.spec (GF := GF) (hG := hG)) :
    apply.authApplierV3.LeaseRevoke.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq id log Pre Q Post info
  wp_start as ⟨#Hauth, #Hinner, Hpre⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, ⟨%le, #Hlef, #Hle⟩, -⟩
  iunfold apply.revokePre at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hwt, Hm⟩
  -- D14h: no lease revocation in the workload
  have hF := Hk.2.2
  simp only [apply.rqOk, Hk.2.1] at hF

end proof

end EtcdGrove
end Perennial
