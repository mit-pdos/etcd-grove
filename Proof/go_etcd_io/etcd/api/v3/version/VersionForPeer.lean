/-
Proof of `Spec/go_etcd_io/etcd/api/v3/version/VersionForPeer.lean` (etcd#22261). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.version.VersionForPeer
public import Spec.github_com.Masterminds.semver.v3.Version__LessThan
public import Perennial.Proof.strings

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.version.Assumptions]

theorem version.VersionForPeer.wp_proof
    (hLT : semver.Version.LessThan.spec (GF := GF) (hG := hG)) :
    version.VersionForPeer.spec (GF := GF) (hG := hG) := by
  intro p ver
  wp_start as #Hver
  wp_auto
  ihave #Hvi : iprop((∃ v : GoString, globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ v) ∗
      (∃ v : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗
      (∃ v : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_8 ↦□ v ∗
        ⌜v.major' = 3 ∧ v.minor' = 8 ∧ v.patch' = 0⌝)) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hvi with ⟨-, -, ⟨%v38, #Hv38, %H38v⟩⟩
  have Ht38 : semver.triple v38 = (3, 8, 0) := by
    simp only [semver.triple, H38v.1, H38v.2.1, H38v.2.2]; decide
  ihave %H38 := typedPointsto_not_null _ _ _ $$ Hv38
  ihave #Hpstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hpsem : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  by_cases hp : p = null
  · subst hp
    simp only [decide_true]
    wp_pures
    wp_apply (IntoValTyped.wp_load (t := go.string) _ _ _) $$ Hver as Hver'
    wp_apply strings.wp_TrimPrefix
    wp_pures
    iapply HΦ
    isplitl
    · ipureintro
      exact ⟨fun _ => rfl, Or.inr rfl⟩
    · iintro %pv Hpv
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
      exact absurd rfl Hnn
  · simp only [hp, decide_false]
    wp_pures
    wp_apply (IntoValTyped.wp_load (t := go.GoType.PointerType
      github_com.Masterminds.semver.v3.Version.ty) _ _ _) $$ peerVer as peerVer
    wp_apply hLT $$ [] as %b Hb
    · itrivial
    cases b
    · wp_pures
      wp_apply (IntoValTyped.wp_load (t := go.string) _ _ _) $$ Hver as Hver'
      wp_pures
      iapply HΦ
      isplitr
      · ipureintro
        exact ⟨fun h => absurd h hp, Or.inl rfl⟩
      · iintro %pv #Hpv
        ihave %Hlt := Hb $$ %pv %v38 Hpv Hv38
        rw [Ht38] at Hlt
        ipureintro
        exact ⟨fun h => absurd (Hlt.1 h) (by simp), fun _ => rfl⟩
    · wp_pures
      wp_apply (IntoValTyped.wp_load (t := go.string) _ _ _) $$ Hver as Hver'
      wp_apply strings.wp_TrimPrefix
      wp_pures
      iapply HΦ
      isplitr
      · ipureintro
        exact ⟨fun h => absurd h hp, Or.inr rfl⟩
      · iintro %pv #Hpv
        ihave %Hlt := Hb $$ %pv %v38 Hpv Hv38
        rw [Ht38] at Hlt
        ipureintro
        exact ⟨fun _ => rfl, fun h => absurd (Hlt.2 h) (by simp)⟩

end proof

end EtcdGrove
end Perennial
