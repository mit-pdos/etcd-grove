/-
Proof of `Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__BackendPath.lean` (bkarea, 2026-11-22;
until then a trust-boundary axiom, D22 S-f, 2026-10-19): `BackendPath()` is
`datadir.ToBackendFileName(c.DataDir)`, whose spec returns `filepath.Join(d, "member", "snap") + "/db"`,
`config.backendPathOf d` by definition.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__BackendPath
public import Spec.go_etcd_io.etcd.server.v3.storage.datadir.ToBackendFileName

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

theorem config.ServerConfig.BackendPath.wp_proof
    (wp_ToBackendFileName : datadir.ToBackendFileName.spec (GF := GF) (hG := hG)) :
    config.ServerConfig.BackendPath.spec (GF := GF) (hG := hG) := by
  intro c dq d hd
  wp_start as Hf
  wp_auto
  wp_apply wp_ToBackendFileName d hd
  (try wp_auto)
  have e : path.joinModel [d, go!"member", go!"snap"] ++ [path.slash] ++ go!"db" =
      config.backendPathOf d := by
    simp [config.backendPathOf, config.snapDirOf]; rfl
  rw [e]
  iapply HΦ
  iexact Hf

end proof

end EtcdGrove
end Perennial
