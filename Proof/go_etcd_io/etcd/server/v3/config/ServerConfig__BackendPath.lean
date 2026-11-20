/-
Trust boundary: `config.ServerConfig.BackendPath` (an axiom; see
`Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__BackendPath.lean`). D22 S-f, 2026-10-19;
`notes/decisions.md`, "D22 S-f carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__BackendPath

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (D22 S-f): `BackendPath()` is `datadir.ToBackendFileName(c.DataDir)`,
`filepath.Join(c.DataDir, "member", "snap", "db")`: a pure function of the field, `backendPathOf`,
with no other effect. (wal-link, 2026-11-19, option B1) `backendPathOf d` is the name `db` in the
snapshot directory `snapDirOf d` (opaque: `c.SnapDir()`), so this axiom also claims that
`BackendPath()` is `SnapDir() + "/db"` (`config/Defs.lean`'s header; the Go test
`examples/etcd/snappaths/snappaths_test.go`). What would discharge it: translating `datadir` with
its body over a spec of `filepath.Join` (and `snapDirOf` defined as it). -/
axiom config.ServerConfig.BackendPath.wp_proof :
  config.ServerConfig.BackendPath.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
