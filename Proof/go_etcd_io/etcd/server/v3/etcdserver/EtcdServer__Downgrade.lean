/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Downgrade.lean`. Lean-first (no
Rocq counterpart).
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

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.Downgrade.wp_proof
    (hValidate : EtcdServer.downgradeValidate.spec (GF := GF) (hG := hG))
    (hEnable : EtcdServer.downgradeEnable.spec (GF := GF) (hG := hG))
    (hCancel : EtcdServer.downgradeCancel.spec (GF := GF) (hG := hG)) :
    EtcdServer.Downgrade.spec (GF := GF) (hG := hG) := by
  intro s l r act ver ctx EP CP
  wp_start as ⟨#Hok, Hrd, #Hum, #Hact, #Hver, HEP, HCP⟩
  iunfold dgErrVar at Hum
  icases Hum with ⟨%eU, #HeU⟩
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_apply hValidate s l EP CP ctx ver $$ [Hrd] as %resp %err ⟨Hrd, Hpost⟩
    · iframe #; iframe Hrd
    (try wp_auto)
    iapply HΦ
    iframe Hrd
    ileft
    iframe Hpost HEP HCP
    try (ipureintro; first | rfl | assumption)
  · wp_if_destruct
    · (try wp_auto)
      wp_apply hEnable s l r ver ctx EP CP $$ [Hrd HEP] as %resp %err ⟨Hrd, Hpost⟩
      · iframe #; iframe Hrd HEP
      (try wp_auto)
      iapply HΦ
      iframe Hrd
      iright; ileft
      iframe Hpost HCP
      try (ipureintro; first | rfl | assumption)
    · wp_if_destruct
      · (try wp_auto)
        wp_apply hCancel s l ctx EP CP $$ [Hrd HCP] as %resp %err ⟨Hrd, Hpost⟩
        · iframe #; iframe Hrd HCP
        (try wp_auto)
        iapply HΦ
        iframe Hrd
        iright; iright; ileft
        iframe Hpost HEP
        try (ipureintro; first | rfl | assumption)
      · (try wp_auto)
        iapply HΦ
        iframe Hrd
        iright; iright; iright
        iframe HEP HCP
        isplitr
        · ipureintro; exact ⟨by assumption, by assumption, by assumption, rfl⟩
        iunfold dgErrIs
        iexists eU
        iframe HeU
        ipureintro; rfl

end proof

end EtcdGrove
end Perennial
