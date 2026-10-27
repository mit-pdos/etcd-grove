/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/checkVersionCompatibility.lean`
(rafthttp stage 6e, 2026-10-24). Lean-first.
-/
module

public import Proof.github_com.Masterminds.semver.v3.MustParsePure
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkVersionCompatibility
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.compareMajorMinorVersion
public import Spec.github_com.Masterminds.semver.v3.MustParse
public import Spec.github_com.Masterminds.semver.v3.Version__String
public import Spec.fmt.Errorf
public import Proof.github_com.Masterminds.semver.v3.Simple

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- A version (not `nil`), as an `fmt` argument: its `String()` returns (`fmt.argOk`). -/
theorem semver_stringMethodSpec (hString : semver.Version.String.spec (GF := GF) (hG := hG))
    (v : Loc) (hv : v ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ⊢
      fmt.stringMethodSpec ⟨go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty, #v⟩
        go!"String" := by
  iintro #Hp
  rw [fmt.stringMethodSpec_unfold]
  iintro !> %Φ HΦ
  iapply hString v $$ []
  · iframe #; ipureintro; exact hv
  inext
  iintro %s -
  iapply HΦ

theorem rafthttp.checkVersionCompatibility.wp_proof
    (hMP : semver.MustParse.spec (GF := GF) (hG := hG))
    (hCompare : rafthttp.compareMajorMinorVersion.spec (GF := GF) (hG := hG))
    (hString : semver.Version.String.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    rafthttp.checkVersionCompatibility.spec (GF := GF) (hG := hG) := by
  intro name server minCluster Hs Hm
  wp_start as -
  ihave #Hpver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Hvi : iprop(globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ go!"3.8.0-alpha.0" ∗
      (∃ v : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗
      globalAddr go_etcd_io.etcd.api.v3.version.MinClusterVersion ↦□ go!"3.0.0") $$ []
  · iapply isPkgInit_access $$ Hpver
  icases Hvi with ⟨#HVer, -, #HMCV⟩
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  ihave #Hfp : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply (semver.MustParse.pure hMP _) as %lsv %Hls
  obtain ⟨ls, rfl, Hlsnn⟩ : ∃ v : Loc, lsv = #v ∧ v ≠ null := by
    rcases Hls with ⟨-, h⟩ | ⟨Hn, -⟩
    · exact h
    · exact absurd (semver.semverValid_simple _ (by decide)) Hn
  (try wp_auto)
  wp_apply (semver.MustParse.pure hMP _) as %lmv %Hlm
  obtain ⟨lm, rfl, Hlmnn⟩ : ∃ v : Loc, lmv = #v ∧ v ≠ null := by
    rcases Hlm with ⟨-, h⟩ | ⟨Hn, -⟩
    · exact h
    · exact absurd (semver.semverValid_simple _ (by decide)) Hn
  (try wp_auto)
  wp_apply hCompare server lm Hs Hlmnn as %c1 -
  (try wp_auto)
  wp_if_destruct
  · wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply hErrorf _ _ _ _ $$ [Hasl] as %e -
    · iframe #; iframe Hasl
      simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl,
        List.set_cons_succ, List.set_cons_zero, fmt.argsOk, fmt.argOk]
      isplitr
      · ileft; ipureintro
        apply fmt.argWf_of_argsWf
        exact .cons_string _ _ .nil
      isplitr
      · iright; iright; iapply semver_stringMethodSpec hString server Hs $$ Hsp
      isplitr
      · iright; iright; iapply semver_stringMethodSpec hString ls Hlsnn $$ Hsp
      itrivial
    (try wp_auto)
    iapply HΦ; ipureintro; exact ⟨Hlsnn, Hlmnn⟩
  (try wp_auto)
  wp_apply hCompare minCluster ls Hm Hlsnn as %c2 -
  (try wp_auto)
  wp_if_destruct
  · wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply hErrorf _ _ _ _ $$ [Hasl] as %e -
    · iframe #; iframe Hasl
      simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl,
        List.set_cons_succ, List.set_cons_zero, fmt.argsOk, fmt.argOk]
      isplitr
      · ileft; ipureintro
        apply fmt.argWf_of_argsWf
        exact .cons_string _ _ .nil
      isplitr
      · iright; iright; iapply semver_stringMethodSpec hString server Hs $$ Hsp
      isplitr
      · iright; iright; iapply semver_stringMethodSpec hString ls Hlsnn $$ Hsp
      itrivial
    (try wp_auto)
    iapply HΦ; ipureintro; exact ⟨Hlsnn, Hlmnn⟩
  (try wp_auto)
  iapply HΦ; ipureintro; exact ⟨Hlsnn, Hlmnn⟩

end proof

end EtcdGrove
end Perennial
