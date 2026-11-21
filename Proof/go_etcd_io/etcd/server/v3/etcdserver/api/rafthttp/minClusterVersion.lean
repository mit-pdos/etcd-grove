/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/minClusterVersion.lean` (rafthttp stage
6e, 2026-10-24; `serverVersion`'s, at `X-Min-Cluster-Version`). Lean-first.
-/
module

public import Proof.github_com.Masterminds.semver.v3.MustParsePure
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.minClusterVersion
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

theorem rafthttp.minClusterVersion.wp_proof
    (hHeaderGetPtr : http.HeaderGetPtr_spec (GF := GF))
    (hMP : semver.MustParse.spec (GF := GF) (hG := hG)) :
    rafthttp.minClusterVersion.spec (GF := GF) (hG := hG) := by
  intro hm hs
  wp_start as #Hhs
  wp_auto
  ipersist h
  wp_apply hHeaderGetPtr _ hm hs _ $$ []
  · iframe #
  (try wp_auto)
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  by_cases he : http.hdrGet hs go!"X-Min-Cluster-Version" = []
  · -- unset: `"2.0.0"`, valid
    rw [he]
    simp only [↓reduceIte]
    (try wp_auto)
    wp_apply (semver.MustParse.valid hMP _ (semver.semverValid_simple _ (by decide)))
      as %nv %xnv ⟨%Hnv, #Hx⟩
    (try wp_auto)
    iapply HΦ; ileft; iexists nv, xnv; iframe #; ipureintro; exact ⟨rfl, Hnv⟩
  · (try simp only [_root_.decide_eq_false he])
    (try wp_auto)
    wp_apply (semver.MustParse.ver hMP _) as %rv Hrv
    icases Hrv with (⟨%nv, %xnv, %Hc, #Hx⟩ | %Hc)
    · obtain ⟨-, rfl, Hnv⟩ := Hc
      (try wp_auto)
      iapply HΦ; ileft; iexists nv, xnv; iframe #; ipureintro; exact ⟨rfl, Hnv⟩
    · -- the header does not parse: `MustParse` panics
      obtain ⟨-, p, rfl⟩ := Hc
      wp_auto
      iapply HΦ; iright; ipureintro
      exact ⟨p, rfl⟩

end proof

end EtcdGrove
end Perennial
