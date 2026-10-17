/-
The downgrade API's results (pr-verify etcd#22589), with the trust base of each printed in the
build log (`#print axioms`). Lean-first (no Rocq counterpart).

* The linked results of the version manager's `DowngradeValidate`, `DowngradeEnable`,
  `DowngradeCancel` and `allowedDowngradeVersion`, and of the server's `Downgrade`,
  `downgradeValidate`, `downgradeEnable`, `downgradeCancel` (the server's `Link.lean`): no panic
  for any cluster version the server reports, `nil` included, at every read.
* **The PR's manager-level test as theorems** (`TestDowngradeValidateNilClusterVersion`, over
  `nilVersionMemberMock`): a manager whose server's linearizable read succeeds and whose cluster
  version is not decided (`GetClusterVersion()` returns `nil`) answers `DowngradeValidate`
  (`validate_nilClusterVersion`) and `DowngradeEnable` (`enable_nilClusterVersion`) with
  `ErrClusterVersionUnavailable`; the enable proposes nothing (its proposal right `EP` is given
  back).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.version

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A `nil`-version server's outcome of `DowngradeValidate`: `ErrClusterVersionUnavailable`. -/
theorem version.validateOutcome_nilServer (err : GoInterface) :
    version.validateOutcome (GF := GF) (fun e => iprop(⌜e = GoInterface.nil⌝))
      (fun cv => iprop(⌜cv = null⌝)) err ⊢
      dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable err := by
  unfold version.validateOutcome
  iintro (⟨%h, %h'⟩ | ⟨#H, -, -⟩ | ⟨%cv, %hcv, -, %h, -⟩)
  · exact absurd h' h
  · iexact H
  · exact absurd h hcv

theorem version.validate_nilClusterVersion (m : Loc) (vs : GoInterface) (EP CP : IProp GF)
    (ctx : GoInterface) (tv : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version ∗
        version.versionFacts ∗
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.version.Manager go!"s" m ↦□ vs ∗
        version.isServer vs (fun e => iprop(⌜e = GoInterface.nil⌝)) (fun cv => iprop(⌜cv = null⌝))
          EP CP ∗ ⌜tv ≠ null⌝ }}
      (App (App (Val (m @!! go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.version.Manager.ty @!! go!"DowngradeValidate"))
        (Val #ctx)) (Val #tv))
    {{ (err : GoInterface), RET #err;
        dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable err }} := by
  iintro %Φ Hpre HΦ
  iapply (version.Manager.wp_DowngradeValidate m vs _ _ EP CP ctx tv) $$ Hpre
  inext
  iintro %err Hout
  iapply HΦ
  iapply version.validateOutcome_nilServer $$ Hout

theorem version.enable_nilClusterVersion (m : Loc) (vs : GoInterface) (EP CP : IProp GF)
    (ctx : GoInterface) (tv : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version ∗
        version.versionFacts ∗
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.version.Manager go!"s" m ↦□ vs ∗
        version.isServer vs (fun e => iprop(⌜e = GoInterface.nil⌝)) (fun cv => iprop(⌜cv = null⌝))
          EP CP ∗ ⌜tv ≠ null⌝ ∗ EP }}
      (App (App (Val (m @!! go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.version.Manager.ty @!! go!"DowngradeEnable"))
        (Val #ctx)) (Val #tv))
    {{ (err : GoInterface), RET #err;
        dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable err ∗
        EP }} := by
  iintro %Φ Hpre HΦ
  iapply (version.Manager.wp_DowngradeEnable m vs _ _ EP CP ctx tv) $$ Hpre
  inext
  iintro %err Hout
  iapply HΦ
  icases Hout with (⟨-, Hout, HEP⟩ | ⟨%cv, %hcv, -, %h⟩)
  · iframe HEP
    iapply version.validateOutcome_nilServer $$ Hout
  · exact absurd h hcv

end results

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.version.wp_allowedDowngradeVersion
#print axioms Perennial.EtcdGrove.version.Manager.wp_DowngradeValidate
#print axioms Perennial.EtcdGrove.version.Manager.wp_DowngradeEnable
#print axioms Perennial.EtcdGrove.version.Manager.wp_DowngradeCancel
#print axioms Perennial.EtcdGrove.version.validate_nilClusterVersion
#print axioms Perennial.EtcdGrove.version.enable_nilClusterVersion
#print axioms Perennial.EtcdGrove.EtcdServer.wp_downgradeValidate
#print axioms Perennial.EtcdGrove.EtcdServer.wp_downgradeEnable
#print axioms Perennial.EtcdGrove.EtcdServer.wp_downgradeCancel
#print axioms Perennial.EtcdGrove.EtcdServer.wp_Downgrade
