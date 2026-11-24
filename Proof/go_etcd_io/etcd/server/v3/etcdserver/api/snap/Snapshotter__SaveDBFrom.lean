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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `(*Snapshotter).SaveDBFrom(r, id)` (`snap/db.go:37-90`) copies `r` to its end into a temporary file, fsyncs it and renames it to the index's path (or keeps a file already there), the directory's ghost steps as the spec's header says. What would discharge it: `snap/db.go` translated with the file system's model (D22). (S5, 2026-11-18) The invariant's files are concrete file-extension state (`backend.fileAt`): at the link of an index the directory has never saved (`E` has it not), the ghost step takes the index's free name from the invariant (`snapFree`: the claim on it, naming no file) and puts back the file holding the image of `D` (`fileAt`, the claim with the file: what a model body does under that claim, creating the file, writing the stream's bytes, syncing; the temporary file is the body's scratch, under a `tmp*` name whose claim is the invariant's alone (`snap.snapDirOwn`, the claim on the directory's names but `db` and the canonical ones, which `snapDirInv` holds; claim #34, 2026-11-23: until then no one's), the body's create and remove of it steps on that claim, so a body realizing the spec writes under the index's name); at a kept file nothing. So the axiom consumes the exclusive claim it fills and makes none: it cannot give a second file at a name. -/
axiom snap.Snapshotter.SaveDBFrom.wp_proof : snap.Snapshotter.SaveDBFrom.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
