/-
**The server configuration's paths** (D22 S-f, 2026-10-19; wal-link, 2026-11-19, decided by
etcd-grove-03, option B1; wal-fsfix2, 2026-11-20, approved by the user: `snapDirOf` defined):
`snapDirOf dataDir`, the snapshot directory of the data directory `dataDir`
(`ServerConfig.SnapDir()`: `filepath.Join(datadir.ToMemberDir(DataDir), "snap")`, i.e.
`filepath.Join(DataDir, "member", "snap")`, Go's own function: `path.joinModel`, the model
`filepath.Join`'s proof returns, `Spec/path/filepath/Join.lean`), and `backendPathOf dataDir`, the
backend's database file (`ServerConfig.BackendPath()`: `datadir.ToBackendFileName(DataDir)`,
`filepath.Join(DataDir, "member", "snap", "db")`), defined as the name `db` in that directory, which
`Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__BackendPath.lean` returns and the backend's
opening (`storage.OpenBackend`) opens. Lean-first (no Rocq counterpart).

Why `snapDirOf dd` is `filepath.Join(dd, "member", "snap")`: `SnapDir()` is
`filepath.Join(filepath.Join(dd, "member"), "snap")`, and joining in two steps gives what joining in
one does (`Clean` of a cleaned prefix and more elements is `Clean` of the whole). Why `backendPathOf
dd` is `snapDirOf dd ++ "/db"` (Go: `server/storage/datadir/datadir.go`,
`ToBackendFileName(dataDir) = filepath.Join(ToSnapDir(dataDir), "db")`, `ToSnapDir(dataDir) =
filepath.Join(ToMemberDir(dataDir), "snap")`; `config.go`: `SnapDir() = filepath.Join(c.MemberDir(),
"snap")`, `MemberDir() = datadir.ToMemberDir(c.DataDir)`): `filepath.Join` cleans its result, and a
cleaned path ending in the element `snap` does not end in `/`, so joining it with the clean name `db`
appends `/db`. The Go test `examples/etcd/snappaths/snappaths_test.go` checks both on data
directories relative, absolute, empty, `/`, with `.`, `..` and repeated or trailing slashes. Until
2026-11-19 `backendPathOf` was opaque, unrelated to the snapshot files' paths (until 2026-11-19
`snap.snapDBPathOf`, now `snap.snapDBPath (snapDirOf dd) i`, `snapDirOf dd ++ "/" ++ <i>.snap.db`),
so the model could not see that `OpenSnapshotBackend`'s rename stays in one directory. From
2026-11-19 to 2026-11-20 `snapDirOf` was opaque, so the paths' lengths (`Fs.PathFits`, which
`bootOk`'s claims carry) were asserted by the bootstrap contract; now they follow from the data
directory's (`config/PathFits.lean`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import GooseLang.Ext.Fs.Paths
public import Proof.path.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace config

/-- **The snapshot directory of the data directory `dataDir`** (see the file header): `cfg.SnapDir()`,
Go's `filepath.Join(dataDir, "member", "snap")` (until 2026-11-20 opaque). -/
def snapDirOf (dataDir : GoString) : GoString :=
  path.joinModel [dataDir, go!"member", go!"snap"]

/-- **The backend's database file of the data directory `dataDir`**: the name `db` in its snapshot
directory (see the file header; until 2026-11-19 opaque). -/
def backendPathOf [GooseExts] (dataDir : GoString) : GoString :=
  snapDirOf dataDir ++ slashB :: go!"db"

end config
end EtcdGrove
end Perennial
