/-
Trust boundary: `snap.Snapshotter.SaveDBFrom` (an axiom; see `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__SaveDBFrom.lean`). rafthttp stage 7e, 2026-10-25, D42. **D22's interface, settled by the user for the D22 owner (2026-10-25).**
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__SaveDBFrom

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `(*Snapshotter).SaveDBFrom(r, id)` (`snap/db.go:37-90`) copies `r` to its end into a temporary file, fsyncs it and renames it to the index's path (or keeps a file already there), the directory's ghost steps as the spec's header says. What would discharge it: `snap/db.go` translated with the file system's model (D22). -/
axiom snap.Snapshotter.SaveDBFrom.wp_proof : snap.Snapshotter.SaveDBFrom.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
