/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__addSubstream.lean` (the watch slice's
unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__addSubstream
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.addSubstream.wp_proof
    (wp_rpctypes_Error : rpctypes.Error.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.addSubstream.spec (GF := GF) (hG := hG) := by
  intro V wgs resp ws id ca rs dq dq' wid0 m M e
  wp_start as ⟨#Hcf, Hid, Hca, Hrs, Hwid, Hsub, Hmap, Hce, Hcl⟩
  iunfold watchConnFacts at Hcf
  icases Hcf with ⟨-, -, -, -, -, -, -, -, #HeN, -, -, -⟩
  iunfold errorsNewOk at HeN
  (try wp_auto)
  wp_if_destruct
  · rw [ite_eq_left (decide_eq_true (by unfold addFails at *; simp_all))]
    ihave Hcl := Hcl $$ %(by unfold addFails at *; simp_all)
    iunfold recvcCloser at Hcl
    icases Hcl with ⟨%P, %sent, %HPws, #Hws, Hprod⟩
    subst HPws
    iunfold wsIs at Hws
    icases Hws with ⟨-, -, #Hrecvc, -, -, #Hspsc, -⟩
    (try wp_auto)
    wp_bind (App (Val #(functions _root_.Perennial.errors.New [])) (Val #rs))
    iapply HeN
    inext
    iintro %e1 %He1 #Hs1
    (try wp_auto)
    ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
    · iPkgInit
    wp_apply wp_rpctypes_Error e1 $$ [$Hrpc $Hs1] as %e2 ⟨%He2, #Hs2, -⟩
    · ipureintro; exact He1.1
    (try wp_auto)
    wp_apply wp_spsc_close P.γr P.recvc (recvElem V P) (fun _ => iprop(True)) sent $$ [$Hspsc $Hprod]
    (try wp_auto)
    iapply HΦ
    iframe
    iexact Hs2
  wp_if_destruct
  · rw [ite_eq_right (by rw [decide_eq_true_iff]; unfold addFails at *; simp_all)]
    (try wp_auto)
    wp_apply wp_mapInsert $$ [$Hmap] as Hmap
    (try wp_auto)
    iapply HΦ
    iframe
  cases hrs : decide (rs = [])
  · simp only [Bool.not_false]
    rw [ite_eq_left (decide_eq_true (by unfold addFails at *; simp_all))]
    ihave Hcl := Hcl $$ %(by unfold addFails at *; simp_all)
    iunfold recvcCloser at Hcl
    icases Hcl with ⟨%P, %sent, %HPws, #Hws, Hprod⟩
    subst HPws
    iunfold wsIs at Hws
    icases Hws with ⟨-, -, #Hrecvc, -, -, #Hspsc, -⟩
    (try wp_auto)
    wp_bind (App (Val #(functions _root_.Perennial.errors.New [])) (Val #rs))
    iapply HeN
    inext
    iintro %e1 %He1 #Hs1
    (try wp_auto)
    ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
    · iPkgInit
    wp_apply wp_rpctypes_Error e1 $$ [$Hrpc $Hs1] as %e2 ⟨%He2, #Hs2, -⟩
    · ipureintro; exact He1.1
    (try wp_auto)
    wp_apply wp_spsc_close P.γr P.recvc (recvElem V P) (fun _ => iprop(True)) sent $$ [$Hspsc $Hprod]
    (try wp_auto)
    iapply HΦ
    iframe
    iexact Hs2
  · simp only [Bool.not_true]
    rw [ite_eq_right (by rw [decide_eq_true_iff]; unfold addFails at *; simp_all)]
    (try wp_auto)
    wp_apply wp_mapInsert $$ [$Hmap] as Hmap
    (try wp_auto)
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
