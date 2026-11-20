/-
Trust boundary: `snap.Snapshotter.ReleaseSnapDBs` (an axiom; see
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__ReleaseSnapDBs.lean`). wal-link L2,
2026-11-17; reviewed twice (`notes/axiom-review/releasesnapdbs.md`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__ReleaseSnapDBs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `(*Snapshotter).ReleaseSnapDBs(snap)` (`snap/snapshotter.go:45-72`) lists the
directory and removes the `.snap.db` entries below the snapshot's index, as the spec's docstring says.
What would discharge it: `snapshotter.go` translated with the file system's model. -/
axiom snap.Snapshotter.ReleaseSnapDBs.wp_proof :
  snap.Snapshotter.ReleaseSnapDBs.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
