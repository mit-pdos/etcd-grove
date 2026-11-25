/-
`ss.ReleaseSnapDBs(sn)` (`server/etcdserver/api/snap/snapshotter.go:45-72` at the etcd pin; names
only; wal-link L2, 2026-11-17): the snapshot directory's `.snap.db` files below the snapshot's index
removed. The trust boundary (an axiom, `Proof/.../snap/Snapshotter__ReleaseSnapDBs.lean`); why it is
true of the Go code in the docstring below. Reviewed twice (`notes/axiom-review/releasesnapdbs.md`:
the first text refuted, this one surviving the second round). Lean-first (no Rocq counterpart);
`storage.storage.Release`'s callee.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.raft.v3.InvPb
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI snap go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`ss.ReleaseSnapDBs(sn)`**: `sn`'s metadata read at index `i = md.Index` (a nil `Metadata`
reads `0`), the snapshot directory's invariant at any removal fact `Rm`, with `Rm j` for every
`j < i`: `nil`, or an error when the directory cannot be opened or listed (`¬ dirReadOk ss`).

What Go does: it opens and lists `ss`'s directory (the only errors), and removes each entry whose
name ends in `.snap.db` and whose prefix parses as a base-16 `uint64` below `i`
(`strconv.ParseUint(prefix, 16, 64)`), canonical or not, an empty directory of such a name included;
a failed removal (a non-empty directory, I/O) is logged and skipped, not returned
(`examples/axiomcx/releasesnapdbs`, `TestAttackNames`). Why the statement is true of it:
* A canonical name is `snapDBPath sd j` (`sd` the snapshotter's `dir`, `isSnapshotter ss sd`;
  wal-link, 2026-11-19, until then the opaque `snapDBPath ss`, `notes/snapdir-crossworld.md`). Such a file is in the invariant's `M`, or held by a taker
  (`snapDir_take`, `rafthttp/Net.lean`: it hands out no `fileHolds`, only the sealed token
  `storage.snapHeld` that `OpenSnapshotBackend` consumes at its rename, the seal gated by
  `etc/import-all.txt`), whose premise refutes `Rm j` and which keeps the resource it could make
  `Rm j` from sealed in the token: so no caller of this function holds `Rm j` for a held `j`, and Go
  removes only files in `M` below `i`. At each removal the file leaves `M` with its removal fact
  `Rm j` (given), and its index joins the saved `E` if it was pending (linked by a `SaveDBFrom` not
  yet past its directory sync, D6-T6 2026-11-25: the name may reappear after a crash, an orphan
  later releases remove; `nonissues/etcd-snapdb-removed-before-dirsync.md`); a file whose removal failed leaves `M` too (forgetting its `fileHolds` is sound; a
  later `SaveDBFrom` of `j` keeps the file, `j` saved already). A file linked by a concurrent
  `SaveDBFrom` after the listing is not removed and joins `M`.
* A non-canonical name (`5.snap.db`, 19 digits, uppercase hex) and an empty directory of such a
  name: the claim on every such name of the directory is the invariant's (`snap.snapDirOwn`, the
  claim on all the names but `db` and the canonical ones, which `snapDirInvH` holds for good; claim
  #34, 2026-11-23: until then an environment clause of the opaque `snapDirOwn`), and the claims of a
  directory are disjoint, so no one else holds a claim on such a name, and no proof's resource
  records a file there or a path through it. A removal is a step on the invariant's claim, which
  the body updates (its history is existential). The file system has no fd-relative operation
  (`openat`, `os.Root`) by which a handle on a removed directory could be written.
* Nothing else is touched: `tmp*` files (a concurrent `SaveDBFrom`'s, under the invariant's claim),
  `*.snap`, the backend's `db` (`OpenSnapshotBackend`'s rename target) do not end in `.snap.db`.
The post does not say that the files below `i` are gone (a removal may fail silently): the caller
gets nothing but the invariant kept. -/
abbrev snap.Snapshotter.ReleaseSnapDBs.spec : Prop :=
  ∀ (ss sn mp : Loc) (sd : GoString) (dq dq' : DFrac) (md : SnapshotMetadataM) (γd : GName)
    (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗
      isSnapshotter ss sd ∗
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      snapDirInvH sd γd img Rm ∗
      □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j) }}
    (App (Val (ss @!! go.GoType.PointerType
        _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!!
        go!"ReleaseSnapDBs")) (Val #sn))
  {{ (err : GoInterface), RET #err;
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      ⌜err = GoInterface.nil ∨ ¬ dirReadOk ss⌝ }}

end spec

end EtcdGrove
end Perennial
