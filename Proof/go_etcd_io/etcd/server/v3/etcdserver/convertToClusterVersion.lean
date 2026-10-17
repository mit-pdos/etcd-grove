/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/convertToClusterVersion.lean`. Lean-first (the
downgrade API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.convertToClusterVersion
public import Spec.github_com.Masterminds.semver.v3.NewVersion
public import Spec.github_com.Masterminds.semver.v3.New
public import Spec.github_com.Masterminds.semver.v3.Version__Major
public import Spec.github_com.Masterminds.semver.v3.Version__Minor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem convertToClusterVersion.wp_proof
    (hNV : semver.NewVersion.spec (GF := GF) (hG := hG))
    (hNew : semver.New.spec (GF := GF) (hG := hG))
    (hMaj : semver.Version.Major.spec (GF := GF) (hG := hG))
    (hMin : semver.Version.Minor.spec (GF := GF) (hG := hG)) :
    convertToClusterVersion.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start as #Herr
  ihave #Psv : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  iunfold srvDgErrVars at Herr
  icases Herr with ⟨-, -, #Hwf⟩
  iunfold dgErrVar at Hwf
  icases Hwf with ⟨%ewf, #Hewf⟩
  wp_auto
  wp_apply hNV $$ [] as %ver %err %Hve
  (try wp_auto)
  rcases err with ei | _
  · -- the first parse failed: `v + ".0"`
    (try wp_auto)
    wp_apply hNV $$ [] as %ver2 %err2 %Hve2
    (try wp_auto)
    rcases err2 with ei2 | _
    · (try wp_auto)
      iapply HΦ
      iright
      isplitr
      · ipureintro; rfl
      iunfold dgErrIs
      iexists ewf; iframe Hewf; ipureintro; rfl
    · have Hnn : ver2 ≠ null := by
        rcases Hve2 with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h (by simp)
      (try wp_auto)
      wp_apply hMaj ver2 $$ [] as %maj -
      · iframe #; ipureintro; exact Hnn
      (try wp_auto)
      wp_apply hMin ver2 $$ [] as %mnr -
      · iframe #; ipureintro; exact Hnn
      (try wp_auto)
      wp_apply hNew $$ [] as %w %Hw
      (try wp_auto)
      iapply HΦ
      ileft
      ipureintro; exact ⟨rfl, Hw⟩
  · have Hnn : ver ≠ null := by
      rcases Hve with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (by simp)
    (try wp_auto)
    wp_apply hMaj ver $$ [] as %maj -
    · iframe #; ipureintro; exact Hnn
    (try wp_auto)
    wp_apply hMin ver $$ [] as %mnr -
    · iframe #; ipureintro; exact Hnn
    (try wp_auto)
    wp_apply hNew $$ [] as %w %Hw
    (try wp_auto)
    iapply HΦ
    ileft
    ipureintro; exact ⟨rfl, Hw⟩

end proof

end EtcdGrove
end Perennial
