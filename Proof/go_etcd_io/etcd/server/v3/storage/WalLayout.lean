/-
**The examples' WAL layout** (wal-link P2, 2026-11-19; `notes/wal-link-scope.md` §3.4 P2, approved by
the user 2026-11-17). Lean-first.

Each member's WAL is in a dedicated WAL directory (etcd's `--wal-dir`, `ServerConfig.DedicatedWALDir`),
alone in an area of its own: the member's root `walAreaOf dd` (`/tmp/etcd-grove-wal/<dd>`, `dd` the
member's data directory, `<name>.etcd`), a root of the Linux file extension (`fsExt` resolves only
absolute paths under its roots), present and holding nothing a WAL function may touch at start (the
closed theorems' premise `etcdWalAreasInit`); the WAL directory is the root's `wal`
(`srvWalDirOf dd`). The examples' Go sets `DedicatedWALDir` so (`examples/lib/etcdstart`'s `WALBase`);
the data directory stays relative (`<name>.etcd`), outside every root: the backend's.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- **The directory holding the members' WAL areas** (`examples/lib/etcdstart`'s `WALBase`). -/
def walBase : GoString := go!"/tmp/etcd-grove-wal"

/-- **The WAL area (the `fsExt` root) of the member with data directory `dd`**. -/
def walAreaOf (dd : GoString) : GoString := walBase ++ go!"/" ++ dd

/-- **The dedicated WAL directory of the member with data directory `dd`**: its area's `wal`. -/
def srvWalDirOf (dd : GoString) : GoString := walAreaOf dd ++ go!"/wal"

end EtcdGrove
end Perennial
