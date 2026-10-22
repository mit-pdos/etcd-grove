/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaAlarmer__check
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newBackendQuota

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.quotaAlarmer.check.wp_proof
    (wp_newBackendQuota : v3rpc.newBackendQuota.spec (GF := GF) (hG := hG)) :
    v3rpc.quotaAlarmer.check.spec (GF := GF) (hG := hG) := by
  intro qa s ci r rt hrt
  wp_start as ⟨#Hqa, Hrd⟩
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  iunfold v3rpc.quotaAlarmerAt at Hqa
  icases Hqa with ⟨%name, %lg, %qb, #Hs, #Hname, #Hlg, %Hlgn, #Hqb, %Hbuq⟩
  iunfold v3rpc.quotaRd at Hrd
  icases Hrd with ⟨Hlr, Hbr⟩
  wp_auto
  -- (D22g (A)) the quota of the backend current at the check
  wp_apply wp_newBackendQuota s lg qb name Hbuq $$ [Hlr Hbr] as %qv ⟨#Hiq, Hlr, Hbr⟩
  · iframe; iframe #; ipureintro; exact Hlgn
  iunfold apply.isQuota at Hiq
  icases Hiq with ⟨%qi, %Hqi, #HAv, -⟩
  subst Hqi
  wp_auto
  wp_apply HAv $$ %rt %r as %b %Hb
  · ipureintro; exact hrt
  -- (audit phase B3, D19h) under `backendUnderQuota` the quota answers true: the NOSPACE
  -- alarm's branch (`s.MemberID()`, `s.Alarm`) is not reached
  subst Hb
  wp_auto
  iapply HΦ
  iunfold v3rpc.quotaRd
  iframe

end proof

end EtcdGrove
end Perennial
