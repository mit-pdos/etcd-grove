/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/checkStreamSupport.lean` (rafthttp
stage 6e, 2026-10-24). Lean-first. The version's major and minor (`semver.New`, `String`), the
supported types' slice looked up in `supportedStream` (rafthttp's fact: a read-only map of
read-only slices), the loop over it.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkStreamSupport
public import Spec.github_com.Masterminds.semver.v3.New
public import Spec.github_com.Masterminds.semver.v3.Version__Major
public import Spec.github_com.Masterminds.semver.v3.Version__Minor
public import Spec.github_com.Masterminds.semver.v3.Version__String

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

theorem rafthttp.checkStreamSupport.wp_proof
    (hNew : semver.New.spec (GF := GF) (hG := hG))
    (hMajor : semver.Version.Major.spec (GF := GF) (hG := hG))
    (hMinor : semver.Version.Minor.spec (GF := GF) (hG := hG))
    (hString : semver.Version.String.spec (GF := GF) (hG := hG)) :
    rafthttp.checkStreamSupport.spec (GF := GF) (hG := hG) := by
  intro v t Hv
  wp_start as -
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    %m, %M, #Hss, #Hm, #HM⟩
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply hMajor $$ [] as %ma -
  · iframe #; ipureintro; exact Hv
  wp_apply hMinor $$ [] as %mi -
  · iframe #; ipureintro; exact Hv
  wp_apply hNew as %nv %Hnv
  (try wp_auto)
  wp_apply hString $$ [] as %ks -
  · iframe #; ipureintro; exact Hnv
  (try wp_auto)
  -- `supportedStream[nv.String()]`: a read-only slice (nil if the version is absent)
  wp_apply (wp_map_lookup1 go.string _ m M ks DFrac.discard) $$ [] as -
  · iexact Hm
  ihave #Hts : iprop(∃ ts : List GoString, ((M !! ks).getD (zero_val GoSlice)) ↦*□ ts) $$ []
  · cases hk : M !! ks with
    | none =>
      iexists []
      simp only [Option.getD_none]
      iapply ownSlice_nil
    | some sl =>
      simp only [Option.getD_some]
      iapply HM $$ %ks %sl %hk
  icases Hts with ⟨%ts, #Hts⟩
  ihave %Htsl := ownSlice_len $$ Hts
  (try wp_auto)
  ihave HF : (∃ (k : w64) (sv : GoString), "i" ∷ i_ptr ↦ k ∗ "s" ∷ s_ptr ↦ sv ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z ((M !! ks).getD (zero_val GoSlice)).len⌝ : IProp GF)
    $$ [i s]
  · iexists W64 0, _
    iframe
    ipureintro
    exact ⟨by decide, Htsl.2⟩
  wp_for HF
  obtain ⟨Hk1, Hk2⟩ := Hk
  (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z ((M !! ks).getD (zero_val GoSlice)).len := ⟨Hk1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    list_elem ts (sint.nat k) as st
    wp_apply (wp_load_slice_index _ (sint.Z k) ts DFrac.discard st Hk1) $$ [] as -
    · iframe #; ipureintro; exact Hst_lookup
    (try wp_auto)
    wp_if_destruct
    · wp_for_post
      iapply HΦ; itrivial
    wp_for_post
    iframe
    iexists k + W64 1, _
    iframe
    ipureintro
    constructor <;> word
  · iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
