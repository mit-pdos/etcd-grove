/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/serverVersion.lean`. Lean-first.
-/
module

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.serverVersion.wp_proof
    (hHeaderGetPtr : http.HeaderGetPtr_spec (GF := GF))
    (hMP : semver.MustParse.spec (GF := GF) (hG := hG)) :
    rafthttp.serverVersion.spec (GF := GF) (hG := hG) := by
  intro hm hs Hv
  wp_start as #Hhs
  wp_auto
  ipersist h
  wp_apply hHeaderGetPtr _ hm hs _ $$ []
  · iframe #
  (try wp_auto)
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  -- the string parsed: the header, or `"2.0.0"` if unset; either is valid
  have Hvalid : apply.semverValid
      (if http.hdrGet hs go!"X-Server-Version" = [] then go!"2.0.0"
       else http.hdrGet hs go!"X-Server-Version") := by
    split
    · exact semver.semverValid_simple _ (by decide)
    · rcases Hv with h | h
      · rename_i hne; exact absurd (h.trans goString_empty) hne
      · exact h
  by_cases he : http.hdrGet hs go!"X-Server-Version" = []
  · rw [he] at Hvalid ⊢
    simp only [↓reduceIte] at Hvalid
    (try wp_auto)
    wp_apply hMP as %rv %Hrv
    obtain ⟨nv, rfl, Hnv⟩ : ∃ v : Loc, rv = #v ∧ v ≠ null := by
      rcases Hrv with ⟨-, h⟩ | ⟨Hn, -⟩
      · exact h
      · exact absurd Hvalid Hn
    wp_auto
    iapply HΦ; ipureintro; exact Hnv
  · simp only [he, ↓reduceIte] at Hvalid
    (try simp only [_root_.decide_eq_false he])
    (try wp_auto)
    wp_apply hMP as %rv %Hrv
    obtain ⟨nv, rfl, Hnv⟩ : ∃ v : Loc, rv = #v ∧ v ≠ null := by
      rcases Hrv with ⟨-, h⟩ | ⟨Hn, -⟩
      · exact h
      · exact absurd Hvalid Hn
    wp_auto
    iapply HΦ; ipureintro; exact Hnv

end proof

end EtcdGrove
end Perennial
