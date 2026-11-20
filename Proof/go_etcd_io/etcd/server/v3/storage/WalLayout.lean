/-
**The examples' WAL layout** (wal-link P2, 2026-11-19; `notes/wal-link-scope.md` §3.4 P2, approved by
the user 2026-11-17). Lean-first.

Each member's WAL is in a dedicated WAL directory (etcd's `--wal-dir`, `ServerConfig.DedicatedWALDir`),
alone in an area of its own: the member's root `walAreaOf dd` (`/tmp/etcd-grove-wal/<name>.etcd`, `dd` the
member's data directory `memberDataDir name`), a root of the Linux file extension (`fsExt` resolves only
absolute paths under its roots), present and holding nothing a WAL function may touch at start (the
closed theorems' premise `etcdWalAreasInit`); the WAL directory is the root's `wal`
(`srvWalDirOf dd`). The examples' Go sets `DedicatedWALDir` so (`examples/lib/etcdstart`'s `WALBase`).
(2026-11-19, approved by the user via etcd-grove-03: `notes/datadir-relative-unsat.md`) The data directory is
absolute too, `memberDataDir name` = `/tmp/etcd-grove-data/<name>.etcd` (`etcdstart`'s `DataBase`), a root of
its own, present and empty at start (`etcdWalAreasInit`); until then relative (`<name>.etcd`), which no claim of
the file model names. `walAreaOf` is of the member's name: the data directory's part below `dataBase`.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- **The directory holding the members' WAL areas** (`examples/lib/etcdstart`'s `WALBase`). -/
def walBase : GoString := go!"/tmp/etcd-grove-wal"

/-- **The directory holding the members' data directories** (`examples/lib/etcdstart`'s `DataBase`). -/
def dataBase : GoString := go!"/tmp/etcd-grove-data"

/-- **The data directory of the member `name`** (`DataBase + "/" + name + ".etcd"`, as goose folds it). -/
def memberDataDir (name : GoString) : GoString := (go!"/tmp/etcd-grove-data/" ++ name) ++ go!".etcd"

/-- **The WAL area (the `fsExt` root) of the member with data directory `dd`**: the member's
`<name>.etcd`, the part of `dd = memberDataDir name` below `dataBase`, under `walBase`. -/
def walAreaOf (dd : GoString) : GoString := walBase ++ dd.drop dataBase.length

/-- The member's WAL area: `/tmp/etcd-grove-wal/<name>.etcd`. -/
theorem walAreaOf_memberDataDir (n : GoString) :
    walAreaOf (memberDataDir n) = (go!"/tmp/etcd-grove-wal/" ++ n) ++ go!".etcd" := by
  simp [walAreaOf, memberDataDir, dataBase, walBase, List.append_assoc]

/-- **The dedicated WAL directory of the member with data directory `dd`**: its area's `wal`. -/
def srvWalDirOf (dd : GoString) : GoString := walAreaOf dd ++ go!"/wal"

/-- **The examples' Go spelling of a member's WAL directory** (`etcdstart.WALBase + "/" + name +
".etcd" + "/wal"`, goose folding the constant prefix) is `srvWalDirOf (memberDataDir name)`. -/
theorem srvWalDirOf_lit (n : GoString) :
    ((go!"/tmp/etcd-grove-wal/" ++ n) ++ go!".etcd") ++ go!"/wal" = srvWalDirOf (memberDataDir n) := by
  rw [srvWalDirOf, walAreaOf_memberDataDir]

/-- `memberDataDir` is injective. -/
theorem memberDataDir_inj {n n' : GoString} (h : memberDataDir n = memberDataDir n') : n = n' := by
  unfold memberDataDir at h
  exact List.append_cancel_left (List.append_cancel_right h)

/-- A member's WAL area is not a data directory (their first 16 bytes differ: `.../etcd-grove-w` and
`.../etcd-grove-d`). -/
theorem walAreaOf_ne_memberDataDir (n n' : GoString) : walAreaOf (memberDataDir n) ≠ memberDataDir n' := by
  rw [walAreaOf_memberDataDir]
  unfold memberDataDir
  intro h
  have := congrArg (List.take 17) h
  simp [List.append_assoc] at this

/-- The members' WAL areas are distinct for distinct members. -/
theorem walAreaOf_memberDataDir_inj {n n' : GoString}
    (h : walAreaOf (memberDataDir n) = walAreaOf (memberDataDir n')) : n = n' := by
  rw [walAreaOf_memberDataDir, walAreaOf_memberDataDir] at h
  exact List.append_cancel_left (List.append_cancel_right h)

end EtcdGrove
end Perennial
