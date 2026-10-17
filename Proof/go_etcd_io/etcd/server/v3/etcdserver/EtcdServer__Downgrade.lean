/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Downgrade.lean`. Lean-first (the
downgrade API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Downgrade
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__downgradeValidate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__downgradeEnable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__downgradeCancel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.Downgrade.wp_proof
    (hVal : EtcdServer.downgradeValidate.spec (GF := GF) (hG := hG))
    (hEn : EtcdServer.downgradeEnable.spec (GF := GF) (hG := hG))
    (hCan : EtcdServer.downgradeCancel.spec (GF := GF) (hG := hG)) :
    EtcdServer.Downgrade.spec (GF := GF) (hG := hG) := by
  intro s l γcv known ctx r act ver
  wp_start as ⟨#Hcv, #Hver, #Herr, #Hverr, Hk, #Hlg, %Hlnn, Hrd, #Hr⟩
  iunfold dgRequestIs at Hr
  icases Hr with ⟨#Hract, #Hrver⟩
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    wp_apply hVal s γcv known ctx ver $$ [Hk] as %resp %err Hout
    · iframe #; iexact Hk
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hout
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply hEn s l γcv known ctx r _ ver $$ [Hrd Hk] as %resp %err ⟨Hrd, Hout⟩
      · iframe #; iframe Hrd Hk; isplitr
        · ipureintro; exact Hlnn
        · iunfold dgRequestIs; iframe #
      (try wp_auto)
      iapply HΦ
      iframe Hrd
      iapply dgOutcome_forget $$ Hout
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_apply hCan s l γcv known ctx $$ [Hk] as %resp %err Hout
        · iframe #; iframe Hk; ipureintro; exact Hlnn
        (try wp_auto)
        iapply HΦ
        iframe Hrd
        iunfold dgOutcome
        icases Hout with (H | H)
        · ileft; iexact H
        · iright; iright; iexact H
      · iunfold srvDgErrVars at Herr
        icases Herr with ⟨-, #Hum, -⟩
        iunfold dgErrVar at Hum
        icases Hum with ⟨%eum, #Heum⟩
        (try wp_auto)
        iapply HΦ
        iframe Hrd
        iunfold dgOutcome
        iright; ileft
        isplitr
        · ipureintro; simp
        simp only [Bool.false_eq_true, ite_false]; itrivial

end proof

end EtcdGrove
end Perennial
