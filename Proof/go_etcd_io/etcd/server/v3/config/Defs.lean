/-
**The server configuration's paths** (D22 S-f, 2026-10-19; wal-link, 2026-11-19, decided by
etcd-grove-03, option B1): `snapDirOf dataDir` (opaque), the snapshot directory of the data
directory `dataDir` (`ServerConfig.SnapDir()`: `filepath.Join(datadir.ToMemberDir(DataDir), "snap")`,
the cleaned `<dataDir>/member/snap`), and `backendPathOf dataDir`, the backend's database file
(`ServerConfig.BackendPath()`: `datadir.ToBackendFileName(DataDir)`, `filepath.Join(DataDir,
"member", "snap", "db")`), defined as the name `db` in that directory, which
`Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__BackendPath.lean` returns and the backend's
opening (`storage.OpenBackend`) opens. Lean-first (no Rocq counterpart).

Why `backendPathOf dd` is `snapDirOf dd ++ "/db"` (Go: `server/storage/datadir/datadir.go`,
`ToBackendFileName(dataDir) = filepath.Join(ToSnapDir(dataDir), "db")`, `ToSnapDir(dataDir) =
filepath.Join(ToMemberDir(dataDir), "snap")`; `config.go`: `SnapDir() = filepath.Join(c.MemberDir(),
"snap")`, `MemberDir() = datadir.ToMemberDir(c.DataDir)`): `filepath.Join` cleans its result, and a
cleaned path ending in the element `snap` does not end in `/`, so joining it with the clean name `db`
appends `/db`. The Go test `examples/etcd/snappaths/snappaths_test.go` checks it on data directories
relative, absolute, empty, `/`, with `.`, `..` and repeated or trailing slashes. Until 2026-11-19
`backendPathOf` was opaque, unrelated to the snapshot files' paths (`snap.snapDBPathOf`, now
`snapDirOf dd ++ "/" ++ <i>.snap.db`), so the model could not see that `OpenSnapshotBackend`'s rename
stays in one directory.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import GooseLang.Ext.Fs.Paths

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace config

/-- **The snapshot directory of the data directory `dataDir`** (opaque; see the file header):
`cfg.SnapDir()`, the cleaned `<dataDir>/member/snap`. -/
opaque snapDirOf [GooseExts] (dataDir : GoString) : GoString

/-- **The backend's database file of the data directory `dataDir`**: the name `db` in its snapshot
directory (see the file header; until 2026-11-19 opaque). -/
def backendPathOf [GooseExts] (dataDir : GoString) : GoString :=
  snapDirOf dataDir ++ slashB :: go!"db"

end config
end EtcdGrove
end Perennial
