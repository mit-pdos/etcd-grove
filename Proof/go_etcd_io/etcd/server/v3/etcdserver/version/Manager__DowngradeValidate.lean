/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/version/Manager__DowngradeValidate.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeValidate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.allowedDowngradeVersion
public import Spec.github_com.Masterminds.semver.v3.Version__Equal

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

theorem version.Manager.DowngradeValidate.wp_proof
    (hAllowed : version.allowedDowngradeVersion.spec (GF := GF) (hG := hG))
    (hEq : semver.Version.Equal.spec (GF := GF) (hG := hG)) :
    version.Manager.DowngradeValidate.spec (GF := GF) (hG := hG) := by
  intro m vs RE CVR EP CP ctx tv
  wp_start as ⟨#Hf, #Hs, #Hsrv, %Htv⟩
  iunfold version.isServer at Hsrv
  icases Hsrv with ⟨%si, %Hsi, #HLR, #HCV, #HDI, -, -⟩
  subst Hsi
  iunfold version.versionFacts at Hf
  iunfold dgErrVar at Hf
  icases Hf with ⟨⟨%eI, #HeI⟩, ⟨%eP, #HeP⟩, -, ⟨%eC, #HeC⟩⟩
  ihave #Psv : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply HLR $$ %ctx as %err Herr
  (try wp_auto)
  cases err with
  | ok ei =>
    (try wp_auto)
    iapply HΦ
    iunfold version.validateOutcome
    ileft
    iframe Herr
    ipureintro
    intro h; cases h
  | nil =>
    (try wp_auto)
    wp_apply HCV as %cv Hcv
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      iunfold version.validateOutcome
      iright; ileft
      iframe Herr Hcv
      iunfold dgErrIs
      iexists eC
      iframe HeC
      ipureintro; rfl
    · have Hcvnn : cv ≠ null := Hif
      wp_apply hAllowed cv $$ [] as %a %Ha
      · iframe #; ipureintro; exact Hcvnn
      (try wp_auto)
      wp_apply hEq as %b -
      cases b
      · (try wp_auto)
        iapply HΦ
        iunfold version.validateOutcome
        iright; iright
        iexists cv
        iframe Herr Hcv
        isplitr
        · ipureintro; exact Hcvnn
        ileft
        iunfold dgErrIs
        iexists eI
        iframe HeI
        ipureintro; rfl
      · (try wp_auto)
        wp_apply HDI as %di ⟨%Hdi, %d, Hd⟩
        (try wp_auto)
        wp_if_destruct
        · exact absurd rfl Hdi
        · (try wp_auto)
          rcases d with ⟨tvs, en⟩
          cases en
          · (try wp_auto)
            iapply HΦ
            iunfold version.validateOutcome
            iright; iright
            iexists cv
            iframe Herr Hcv
            isplitr
            · ipureintro; exact Hcvnn
            iright; iright
            ipureintro; rfl
          · (try wp_auto)
            iapply HΦ
            iunfold version.validateOutcome
            iright; iright
            iexists cv
            iframe Herr Hcv
            isplitr
            · ipureintro; exact Hcvnn
            iright; ileft
            iunfold dgErrIs
            iexists eP
            iframe HeP
            ipureintro; rfl

end proof

end EtcdGrove
end Perennial
