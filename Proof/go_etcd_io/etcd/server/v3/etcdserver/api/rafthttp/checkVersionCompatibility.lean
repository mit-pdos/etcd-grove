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

/-- A version (read-only), as an `fmt` argument: its `String()` returns (`fmt.argOk`). -/
theorem semver_stringMethodSpec (hString : semver.Version.String.spec (GF := GF) (hG := hG))
    (v : Loc) (x : github_com.Masterminds.semver.v3.Version) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ v ↦□ x ⊢
      fmt.stringMethodSpec ⟨go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty, #v⟩
        go!"String" := by
  iintro ⟨#Hp, #Hv⟩
  rw [fmt.stringMethodSpec_unfold]
  iintro !> %Φ HΦ
  iapply hString v DFrac.discard x $$ []
  · iframe #
  inext
  iintro -
  iapply HΦ

theorem rafthttp.checkVersionCompatibility.wp_proof
    (hMP : semver.MustParse.spec (GF := GF) (hG := hG))
    (hCompare : rafthttp.compareMajorMinorVersion.spec (GF := GF) (hG := hG))
    (hString : semver.Version.String.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    rafthttp.checkVersionCompatibility.spec (GF := GF) (hG := hG) := by
  intro name server minCluster xs xm Hs Hm
  wp_start as ⟨#Hxs, #Hxm⟩
  ihave #Hpver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Hvi : iprop(globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ go!"3.8.0-alpha.0" ∗
      (∃ v : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗
      globalAddr go_etcd_io.etcd.api.v3.version.MinClusterVersion ↦□ go!"3.0.0" ∗
      (∃ v7 v8 : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_7 ↦□ v7 ∗
        globalAddr go_etcd_io.etcd.api.v3.version.V3_8 ↦□ v8)) $$ []
  · iapply isPkgInit_access $$ Hpver
  icases Hvi with ⟨#HVer, -, #HMCV, -⟩
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  ihave #Hfp : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply (semver.MustParse.valid hMP _ (semver.semverValid_simple _ (by decide)))
    as %ls %xls ⟨%Hlsnn, #Hls⟩
  (try wp_auto)
  wp_apply (semver.MustParse.valid hMP _ (semver.semverValid_simple _ (by decide)))
    as %lm %xlm ⟨%Hlmnn, #Hlm⟩
  (try wp_auto)
  wp_apply hCompare server lm xs xlm Hs Hlmnn $$ [] as %c1 -
  · iframe #
  (try wp_auto)
  wp_if_destruct
  · wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply hErrorf _ _ _ _ $$ [Hasl] as %e -
    · iframe #; iframe Hasl
      simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl,
        List.set_cons_succ, List.set_cons_zero]
      fmt_args_intro; simp only [fmt.argOkAt, fmt.argOk]
      isplitr
      · ileft; ipureintro
        apply fmt.argWf_of_argsWf
        exact .cons_string _ _ .nil
      isplitr
      · fmt_arg_method; iright; iright; isplitr
        · iapply semver_stringMethodSpec hString server xs; iframe #
        · ipureintro; fmt_method_facts
      isplitr
      · fmt_arg_method; iright; iright; isplitr
        · iapply semver_stringMethodSpec hString ls xls; iframe #
        · ipureintro; fmt_method_facts
      itrivial
    (try wp_auto)
    iapply HΦ
    isplitr
    · ipureintro; exact ⟨Hlsnn, Hlmnn⟩
    isplitl [] <;> (iexists _; iassumption)
  (try wp_auto)
  wp_apply hCompare minCluster ls xm xls Hm Hlsnn $$ [] as %c2 -
  · iframe #
  (try wp_auto)
  wp_if_destruct
  · wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply hErrorf _ _ _ _ $$ [Hasl] as %e -
    · iframe #; iframe Hasl
      simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl,
        List.set_cons_succ, List.set_cons_zero]
      fmt_args_intro; simp only [fmt.argOkAt, fmt.argOk]
      isplitr
      · ileft; ipureintro
        apply fmt.argWf_of_argsWf
        exact .cons_string _ _ .nil
      isplitr
      · fmt_arg_method; iright; iright; isplitr
        · iapply semver_stringMethodSpec hString server xs; iframe #
        · ipureintro; fmt_method_facts
      isplitr
      · fmt_arg_method; iright; iright; isplitr
        · iapply semver_stringMethodSpec hString ls xls; iframe #
        · ipureintro; fmt_method_facts
      itrivial
    (try wp_auto)
    iapply HΦ
    isplitr
    · ipureintro; exact ⟨Hlsnn, Hlmnn⟩
    isplitl [] <;> (iexists _; iassumption)
  (try wp_auto)
  iapply HΦ
  isplitr
  · ipureintro; exact ⟨Hlsnn, Hlmnn⟩
  isplitl [] <;> (iexists _; iassumption)

end proof

end EtcdGrove
end Perennial
