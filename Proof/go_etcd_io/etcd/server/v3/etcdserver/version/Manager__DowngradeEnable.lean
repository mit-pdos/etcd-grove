/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/version/Manager__DowngradeEnable.lean`. Lean-first (the downgrade
API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeEnable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeValidate

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

theorem version.Manager.DowngradeEnable.wp_proof
    (hVal : version.Manager.DowngradeValidate.spec (GF := GF) (hG := hG)) :
    version.Manager.DowngradeEnable.spec (GF := GF) (hG := hG) := by
  intro m si γcv ctx tv
  wp_start as ⟨#Hm, #Hsrv, #Hlb, #Herr, %Htv⟩
  (try wp_auto)
  wp_apply hVal m si γcv ctx tv $$ [] as %err -
  · iframe #
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ; itrivial
  · iunfold version.managerIs at Hm
    iunfold version.serverOk at Hsrv
    icases Hsrv with ⟨%sv, %Hsi, -, -, -, #HDE, -⟩
    subst Hsi
    (try wp_auto)
    wp_apply HDE $$ [] as %err' -
    · ipureintro; exact Htv
    (try wp_auto)
    iapply HΦ; itrivial


end proof

end EtcdGrove
end Perennial
