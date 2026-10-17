/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/version/Manager__DowngradeCancel.lean`. Lean-first (the downgrade
API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeCancel


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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

theorem version.Manager.DowngradeCancel.wp_proof :
    version.Manager.DowngradeCancel.spec (GF := GF) (hG := hG) := by
  intro m si γcv ctx
  wp_start as ⟨#Hm, #Hsrv, #Herr⟩
  iunfold version.managerIs at Hm
  iunfold version.serverOk at Hsrv
  icases Hsrv with ⟨%sv, %Hsi, #HLRN, -, #HGDI, -, #HDC⟩
  subst Hsi
  iunfold version.dgErrVars at Herr
  icases Herr with ⟨-, -, ⟨%e3, #He3⟩⟩
  (try wp_auto)
  wp_apply HLRN $$ [] as %err -
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ; itrivial
  · (try wp_auto)
    wp_apply HGDI $$ [] as %d ⟨%Hd, %di, Hdi⟩
    (try wp_auto)
    generalize di.Enabled' = en
    cases en
    · (try wp_auto)
      iapply HΦ; itrivial
    · (try wp_auto)
      wp_apply HDC $$ [] as %err' -
      (try wp_auto)
      iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
