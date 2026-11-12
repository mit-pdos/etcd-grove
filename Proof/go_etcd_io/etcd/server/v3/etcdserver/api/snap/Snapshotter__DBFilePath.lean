/-
Trust boundary: `snap.Snapshotter.DBFilePath` (an axiom; see
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__DBFilePath.lean`). D22 S-f,
2026-10-19; `notes/decisions.md`, "D22 S-f carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__DBFilePath

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

/-- **Trust boundary** (D22 S-f): `DBFilePath(id)` reads the snapshotter's directory
(`fileutil.ReadDir`) and returns `dbFilePath(id)` (`filepath.Join(dir, "%016x.snap.db")`) if that
file exists (`fileutil.Exist`), else `ErrNoDBSnapshot` (an `errors.New` error, after a warning on
the snapshotter's logger), or the directory read's `*os.PathError`; it writes nothing. What would
discharge it: translating `snap/db.go` with its body over specs of `fileutil.ReadDir`,
`fileutil.Exist` and `filepath.Join` (a file-system model). -/
axiom snap.Snapshotter.DBFilePath.wp_proof : snap.Snapshotter.DBFilePath.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
