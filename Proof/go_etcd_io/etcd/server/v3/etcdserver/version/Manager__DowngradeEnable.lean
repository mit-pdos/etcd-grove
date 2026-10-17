/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/version/Manager__DowngradeEnable.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeEnable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeValidate

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.version

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

theorem version.Manager.DowngradeEnable.wp_proof
    (hValidate : version.Manager.DowngradeValidate.spec (GF := GF) (hG := hG)) :
    version.Manager.DowngradeEnable.spec (GF := GF) (hG := hG) := by
  intro m vs RE CVR EP CP ctx tv
  wp_start as ⟨#Hf, #Hs, #Hsrv, %Htv, HEP⟩
  ihave #Hsrv' := Hsrv
  iunfold version.isServer at Hsrv'
  icases Hsrv' with ⟨%si, %Hsi, -, -, -, #HEN, -⟩
  (try wp_auto)
  wp_apply hValidate m vs RE CVR EP CP ctx tv $$ [] as %err Hout
  · iframe #; ipureintro; exact Htv
  (try wp_auto)
  cases err with
  | ok ei =>
    (try wp_auto)
    iapply HΦ
    ileft
    iframe Hout HEP
    ipureintro
    intro h; cases h
  | nil =>
    (try wp_auto)
    subst Hsi
    (try wp_auto)
    ihave Hw := version.validateOutcome_nil RE CVR $$ Hout
    wp_apply HEN $$ %ctx %tv [HEP] as %err' -
    · iframe HEP; ipureintro; exact Htv
    iapply HΦ
    iright
    iexact Hw

end proof

end EtcdGrove
end Perennial
