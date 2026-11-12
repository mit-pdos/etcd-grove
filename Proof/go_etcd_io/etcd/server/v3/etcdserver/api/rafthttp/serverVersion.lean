/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/serverVersion.lean`. Lean-first.
-/
module

public import Proof.github_com.Masterminds.semver.v3.MustParsePure
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.serverVersion
public import Spec.github_com.Masterminds.semver.v3.MustParse
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

theorem rafthttp.serverVersion.wp_proof
    (hHeaderGetPtr : http.HeaderGetPtr_spec (GF := GF))
    (hMP : semver.MustParse.spec (GF := GF) (hG := hG)) :
    rafthttp.serverVersion.spec (GF := GF) (hG := hG) := by
  intro hm hs
  wp_start as #Hhs
  wp_auto
  ipersist h
  wp_apply hHeaderGetPtr _ hm hs _ $$ []
  · iframe #
  (try wp_auto)
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  by_cases he : http.hdrGet hs go!"X-Server-Version" = []
  · -- unset: `"2.0.0"`, valid
    rw [he]
    simp only [↓reduceIte]
    (try wp_auto)
    wp_apply (semver.MustParse.pure hMP _) as %rv %Hrv
    obtain ⟨nv, rfl, Hnv⟩ : ∃ v : Loc, rv = #v ∧ v ≠ null := by
      rcases Hrv with ⟨-, h⟩ | ⟨Hn, -⟩
      · exact h
      · exact absurd (semver.semverValid_simple _ (by decide)) Hn
    wp_auto
    iapply HΦ; ipureintro; exact Or.inl ⟨nv, rfl, Hnv⟩
  · (try simp only [_root_.decide_eq_false he])
    (try wp_auto)
    wp_apply (semver.MustParse.pure hMP _) as %rv %Hrv
    rcases Hrv with ⟨Hval, nv, rfl, Hnv⟩ | ⟨Hn, p, rfl⟩
    · wp_auto
      iapply HΦ; ipureintro; exact Or.inl ⟨nv, rfl, Hnv⟩
    · -- the header does not parse: `MustParse` panics
      wp_auto
      iapply HΦ; ipureintro
      refine Or.inr ⟨fun Hv => ?_, p, rfl⟩
      rcases Hv with h | h
      · exact he (h.trans goString_empty)
      · exact Hn h

end proof

end EtcdGrove
end Perennial
