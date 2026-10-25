/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/checkClusterCompatibilityFromHeader.lean`
(rafthttp stage 6e, 2026-10-24). Lean-first. The peer's versions (`serverVersion`,
`minClusterVersion`: each may panic on a header that does not parse, which the spec allows), the
compatibility check (`checkVersionCompatibility`), each failure logged and answered with its error
(`errIncompatibleVersion`, `ErrClusterIDMismatch`), else `nil`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkClusterCompatibilityFromHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.serverVersion
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.minClusterVersion
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkVersionCompatibility
public import Spec.github_com.Masterminds.semver.v3.Version__String
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- A log call (`lg.Warn(...)`): its fields' strings, the call. -/
local macro "zap_log" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hString _ $$ [] as %_ -; (iframe #; ipureintro; assumption))
    | (wp_apply hZString as %_ -)
    | (wp_apply hZError as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | wp_auto)))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem rafthttp.checkClusterCompatibilityFromHeader.wp_proof
    (hHeaderGetPtr : http.HeaderGetPtr_spec (GF := GF))
    (hServerVersion : rafthttp.serverVersion.spec (GF := GF) (hG := hG))
    (hMinCluster : rafthttp.minClusterVersion.spec (GF := GF) (hG := hG))
    (hCheckVC : rafthttp.checkVersionCompatibility.spec (GF := GF) (hG := hG))
    (hString : semver.Version.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG)) :
    rafthttp.checkClusterCompatibilityFromHeader.spec (GF := GF) (hG := hG) := by
  intro lg localID cid hm hs Hlgnn
  wp_start as #Hhs
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, #HIV, #HCM, -⟩
  iunfold EtcdGrove.errorsNewVar at HIV HCM
  icases HIV with ⟨%xIV, #HxIVg, -⟩
  icases HCM with ⟨%xCM, #HxCMg, -⟩
  ihave #Htyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  wp_auto
  ipersist header
  ipersist «localID»
  ipersist «cid»
  wp_apply hHeaderGetPtr _ hm hs _ $$ []
  · iframe #
  (try wp_auto)
  -- the peer's server version, or a panic
  wp_apply hServerVersion hm hs $$ [] as %rsv %Hrsv
  · iframe #
  rcases Hrsv with ⟨rs, rfl, Hrsnn⟩ | ⟨-, p, rfl⟩
  rotate_left
  · wp_auto
    iapply HΦ; ileft; ipureintro; exact Or.inr ⟨p, rfl⟩
  (try wp_auto)
  rw [_root_.decide_eq_false Hrsnn]
  (try wp_auto)
  wp_apply hString rs $$ [] as %rss -
  · iframe #; ipureintro; exact Hrsnn
  (try wp_auto)
  -- the peer's minimum cluster version, or a panic
  wp_apply hMinCluster hm hs $$ [] as %rmv %Hrmv
  · iframe #
  rcases Hrmv with ⟨rm, rfl, Hrmnn⟩ | ⟨p, rfl⟩
  rotate_left
  · wp_auto
    iapply HΦ; ileft; ipureintro; exact Or.inr ⟨p, rfl⟩
  (try wp_auto)
  rw [_root_.decide_eq_false Hrmnn]
  (try wp_auto)
  wp_apply hString rm $$ [] as %rms -
  · iframe #; ipureintro; exact Hrmnn
  (try wp_auto)
  wp_apply (hCheckVC _ rs rm Hrsnn Hrmnn) as %ls %lm %verr ⟨%Hlsnn, %Hlmnn⟩
  (try wp_auto)
  rw [_root_.decide_eq_false Hlsnn]
  (try wp_auto)
  wp_apply hString ls $$ [] as %lss -
  · iframe #; ipureintro; exact Hlsnn
  (try wp_auto)
  rw [_root_.decide_eq_false Hlmnn]
  (try wp_auto)
  wp_apply hString lm $$ [] as %lms -
  · iframe #; ipureintro; exact Hlmnn
  (try wp_auto)
  cases verr with
  | ok ve =>
    -- incompatible: logged, `errIncompatibleVersion`
    (try wp_auto)
    zap_log
    iapply HΦ
    iright
    iexists _
    isplitr
    · ipureintro; rfl
    ileft; iexact HxIVg
  | nil =>
    (try wp_auto)
    wp_apply hHeaderGetPtr _ hm hs _ $$ []
    · iframe #
    (try wp_auto)
    wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %cs -
    · iframe #
    (try wp_auto)
    wp_if_destruct
    · -- the cluster's id: `nil`
      (try wp_auto)
      iapply HΦ; ileft; ipureintro; exact Or.inl rfl
    -- a cluster mismatch: logged, `ErrClusterIDMismatch`
    zap_log
    iapply HΦ
    iright
    iexists _
    isplitr
    · ipureintro; rfl
    iright; iexact HxCMg

end proof

end EtcdGrove
end Perennial
