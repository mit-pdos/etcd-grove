/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fillWithoutRevision

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.header.fillWithoutRevision.wp_proof :
    v3rpc.header.fillWithoutRevision.spec (GF := GF) (hG := hG) := by
  intro hp s A cid mid rh
  wp_start as ⟨#Hhdr, Hw⟩
  iunfold v3rpc.hdrIs at Hhdr
  icases Hhdr with ⟨%revf, #Hcid, #Hmid, #Hsg, #Hrev, #HrevS, #Hrs⟩
  iunfold v3rpc.raftStatusOk at Hrs
  icases Hrs with ⟨#HTerm, #HLeader⟩
  iunfold v3rpc.hdrW at Hw
  icases Hw with ⟨%Hnn, %c, %m, %t, %l, Hc, Hm, Ht, Hl⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_pures
  wp_auto
  wp_apply HTerm as %t' _
  wp_apply HLeader as %l' _
  iapply HΦ
  iunfold v3rpc.hdrFilled
  iframe
  ipureintro; exact Hnn

end proof

end EtcdGrove
end Perennial
