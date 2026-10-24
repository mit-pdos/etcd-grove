/-
Proof of `apply.requestV2.toInternalRaftRequest` (`legacy_request.go`, `etcd#22634`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2__toInternalRaftRequest
public import Spec.regexp.Regexp__MatchString
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.StoreClusterVersionKey
public import Spec.path.Dir
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.MustParseMemberIDFromKey
public import Spec.encoding.json.UnmarshalAttributes

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.server.v3.etcdserver.api
open go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2
open go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.requestV2.toInternalRaftRequest.wp_proof
    (hMatch : regexp.Regexp.MatchString.spec (GF := GF) (hG := hG))
    (hVerKey : membership.StoreClusterVersionKey.spec (GF := GF) (hG := hG))
    (hDir : path.Dir.spec (GF := GF) (hG := hG))
    (hParseID : membership.MustParseMemberIDFromKey.spec (GF := GF) (hG := hG))
    (hJson : json.UnmarshalAttributes.spec (GF := GF) (hG := hG)) :
    apply.requestV2.toInternalRaftRequest.spec (GF := GF) (hG := hG) := by
  intro r_ptr r dq lg rq
  wp_start as ⟨Hr, %Hlg, %Hdec⟩
  ihave Hai : (applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, ⟨-, ⟨%re, #Hre, %Hrenn, %HrePat⟩⟩, -⟩
  ihave #Preg : isPkgInit (PROP := IProp GF) pkg_id.regexp $$ []
  · iPkgInit
  ihave #Pmem : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Ppath : isPkgInit (PROP := IProp GF) pkg_id.path $$ []
  · iPkgInit
  ihave #Pjson : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
  · iPkgInit
  unfold apply.legacyToIRR at Hdec
  split at Hdec
  · contradiction
  rename_i hMeth
  simp only [ne_eq, Decidable.not_not] at hMeth
  icases (typedPointsto_not_null_dup _ _ _) $$ Hr with ⟨Hr, %Hrn⟩
  iStructNamed Hr
  wp_auto
  simp only [hMeth, decide_true, Bool.not_true]
  wp_auto
  wp_apply (hMatch re apply.memberAttrPat r.Path')
  · ipureintro; exact ⟨Hrenn, HrePat⟩
  cases hm : apply.regexpMatch apply.memberAttrPat r.Path'
  · -- ClusterVersionSet (`/0/version`)
    simp only [hm, Bool.false_eq_true, ↓reduceIte] at Hdec
    split at Hdec
    next hPath =>
      injection Hdec with hRq
      subst hRq
      simp only [Bool.not_false]
      wp_auto
      wp_apply hVerKey
      simp only [hPath, decide_true, Bool.not_true]
      wp_auto
      wp_apply (hMatch re apply.memberAttrPat _)
      · ipureintro; exact ⟨Hrenn, HrePat⟩
      rw [← hPath, hm]
      iapply wp_fupd
      wp_auto
      ihave Hr : r_ptr ↦{dq} r $$ [ID Method Path Val]
      · iapply typedPointsto_combine r_ptr _ dq Hrn
        simp only [TypedPointsto.typedPointstoDef, hMeth, hPath]
        iframe
      ihave ⟨«$v0», %Hv0nn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v0»
      iStructNamed «$v0»
      ipersist ID
      ipersist Username
      ipersist AuthRevision
      ihave ⟨«$v1», %Hv1nn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v1»
      iStructNamed «$v1»
      ipersist Ver
      imodintro
      iapply HΦ
      iframe Hr
      iunfold apply.internalRaftRequestValIs
      simp only [apply.legacyClusterVersionIRR, apply.irrEmpty, apply.optReqIs, apply.presentIs,
        apply.headerIs, apply.clusterVersionSetIs]
      rw [show (W64 0 : w64) = 0 from rfl]
      iframe #
      ipureintro
      simp [Hv0nn, Hv1nn]
    · contradiction
  · -- ClusterMemberAttrSet (`/0/members/<hex>/attributes`)
    simp only [hm, ↓reduceIte] at Hdec
    cases hmid : apply.parseMemberIDFromKey (apply.pathDir r.Path')
    · simp [hmid] at Hdec
    case some mid =>
      simp only [hmid] at Hdec
      cases hjson : apply.jsonDecodeAttributes r.Val'
      · simp [hjson] at Hdec
      case some nu =>
        obtain ⟨name, urls⟩ := nu
        simp only [hjson] at Hdec
        injection Hdec with hRq
        subst hRq
        simp only [Bool.not_true]
        wp_auto
        wp_apply (hMatch re apply.memberAttrPat r.Path')
        · ipureintro; exact ⟨Hrenn, HrePat⟩
        rw [hm]
        wp_auto
        wp_apply (hDir r.Path')
        wp_apply (hParseID lg (apply.pathDir r.Path') mid)
        · ipureintro; exact ⟨Hlg, hmid⟩
        wp_apply wp_string_to_bytes as %val_sl ⟨Hval_sl, -⟩
        wp_apply (hJson val_sl r.Val' (DFrac.own 1) attributes_ptr _ name urls)
          $$ [Hval_sl attributes]
        · iframe
          ipureintro; exact hjson
        iintro ⟨Hval_sl, %urls_sl, Hattr, #Hurls⟩
        iStructNamed Hattr
        iapply wp_fupd
        wp_auto
        ihave Hr : r_ptr ↦{dq} r $$ [ID Method Path Val]
        · iapply typedPointsto_combine r_ptr _ dq Hrn
          simp only [TypedPointsto.typedPointstoDef, hMeth]
          iframe
        ihave ⟨«$v0», %Hv0nn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v0»
        iStructNamed «$v0»
        ipersist ID
        ipersist Username
        ipersist AuthRevision
        ihave ⟨«$v1», %Hcmasnn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v1»
        iStructNamed «$v1»
        ipersist Member_ID
        ipersist MemberAttributes
        iclear Name ClientURLs
        ihave ⟨«$v1», %Hv1nn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v1»
        iStructNamed «$v1»
        ipersist Name
        ipersist ClientUrls
        imodintro
        iapply HΦ
        iframe Hr
        iunfold apply.internalRaftRequestValIs
        simp only [apply.legacyMemberAttrIRR, apply.irrEmpty, apply.optReqIs, apply.presentIs,
          apply.headerIs, apply.memberAttrSetIs]
        rw [show (W64 0 : w64) = 0 from rfl]
        iframe #
        ipureintro
        simp [Hv0nn, Hcmasnn, Hv1nn]

end proof

end EtcdGrove
end Perennial
