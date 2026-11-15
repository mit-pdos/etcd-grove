/-
**The snapshotter** (`etcdserver/api/snap`, names only; D22 S-f, 2026-10-19): the vocabulary of
its trust-boundary specs. Lean-first (no Rocq counterpart).

* `isSnapshotter ss` (persistent): `ss` is a `*snap.Snapshotter` (`snap.New(lg, dir)`: its fields,
  the logger and the snapshot directory, set once and read-only after). An opaque predicate
  (`snapshotterRO`) made persistent by its definition: the snapshotter's fields are not modeled.
* `snapDBPath ss i` (opaque): the path of the database snapshot of index `i` in `ss`'s
  directory (`ss.dbFilePath(i)`: `<dir>/<i as 16 hex digits>.snap.db`; Go's parameter is named
  `id`, but it is the snapshot's index, not a member id). `DBFilePath` returns
  it (`Spec/.../snap/Snapshotter__DBFilePath.lean`); the transport's `SaveDBFrom` writes the file
  there (D22 S-i).
* `snapDirOwn p` and `snapDirIs p γd` (restart S6a, M1; approved by the user 2026-11-13 via
  etcd-grove-81): the environment's one-time right to the snapshot directory whose files are at the
  paths `p` (`bootOk`, the first start: the directory holds no `.snap.db` file, and nothing outside
  the server's snapshotters writes `.snap.db` files there), and the persistent record, made once from
  it, of the ghost map `γd` that tracks those files (`snapDirInv`, `Proof/.../rafthttp/Net.lean`).
* `msgIs m ml rc` (persistent; D22 S-i): `m` is a `*snap.Message` (`snap.NewMessage(ml, rc,
  size)`: the raft message `ml`, the reader `rc` wrapped in an exact-size reader, the total size
  and the one-slot `closeC` channel), its fields read-only for good (`NewMessage` writes them
  once; `CloseWithError` reads the reader and sends on `closeC`, `CloseNotify` reads `closeC`). An
  opaque predicate (`msgRO`): `snap.Message` is an axiomatized type, so its fields are not
  modeled. `NewMessage`'s spec makes it (D22 S-h), and only it, of a reader whose `Close` returns
  (`io.rcCloseOk`; sweep repairs 1, S1) and a size in its premise's range (S2); the transport's
  `SendSnapshot` takes it.
* `msgCloseC m c` (persistent; D22 S-h): `m`'s `closeC` is the channel `c` (`NewMessage`'s
  `make(chan bool, 1)`, read by `CloseNotify`). An opaque predicate (`msgCloseRO`), as `msgRO`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace snap

open Iris Iris.BI

/-- **The path of the database snapshot of index `i`** of the snapshotter `ss` (opaque; see the
file header). -/
opaque snapDBPath [GooseExts] (ss : Loc) (i : w64) : GoString

/-- **The path of the database snapshot of index `i` in the data directory `dd`** (opaque; restart
S6a, approved by the user 2026-11-13 via etcd-grove-81): `<dd>/member/snap/<i as 16 hex
digits>.snap.db`, a function of `dd` alone. `i` is the snapshot's index (Go's `dbFilePath(id)`
names it `id`); the member enters only through its data directory `dd`. The bootstrap contracts (`bootOk`, `bootOkR`) say that
the snapshotter `bootstrap` returns has `snapDBPath ss = snapDBPathOf cfg.DataDir`, so that two
incarnations of a member over one data directory write their snapshots to the same files. Go:
`bootstrapSnapshot` returns `snap.New(cfg.Logger, cfg.SnapDir())` (`server/etcdserver/bootstrap.go:252`);
`SnapDir()` is `filepath.Join(c.MemberDir(), "snap")` and `MemberDir()` is
`datadir.ToMemberDir(c.DataDir)` (`server/config/config.go:300,309`); `dbFilePath(id)` is
`filepath.Join(s.dir, fmt.Sprintf("%016x.snap.db", id))` (`server/etcdserver/api/snap/db.go:117-119`),
and `s.dir` is written only by `New` (`snapshotter.go:34-40`). `filepath.Join` is lexical, so the
equation is about strings; that equal path strings name the same file (no change of working
directory between incarnations under a relative `DataDir`, no symbolic link or other alias of the
directory, and a restart under the same `DataDir` string) is the file-system model's assumption that a
path string names one file, as for `config.backendPathOf` and `backend.pathOwn`. No law: only the
equation of the contracts relates it to `snapDBPath`. -/
opaque snapDBPathOf [GooseExts] (dd : GoString) (i : w64) : GoString

/-- The address of the snapshotter `ss`'s logger field (`s.lg`; `snap.Snapshotter` is an
axiomatized type, so the field is named, not modeled). -/
abbrev snapLgAddr [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] (ss : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter go!"lg" ss

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ss`'s fields, read-only (opaque; see the file header). -/
opaque snapshotterRO (ss : Loc) : IProp GF

/-- **`ss` is a snapshotter** (persistent; see the file header), its logger a zap logger
(`zapLoggerOk`; premise fixes 6: `SaveDBFrom` logs through it; `snap.New(lg, dir)` stores `lg`,
nil replaced by `zap.NewNop()`). -/
def isSnapshotter (ss : Loc) : IProp GF :=
  iprop(□ snapshotterRO ss ∗ ∃ lg : Loc, snapLgAddr ss ↦□ lg ∗ zapLoggerOk lg)

/-- **The snapshotter `ss`'s directory reads** (opaque, a named premise about the program's
environment; D22 receiver epochs, S8d, 2026-10-24): listing `ss`'s directory does not fail
(`DBFilePath`'s `fileutil.ReadDir`), and a `.snap.db` file the program holds there is found. The
premise excluding the failure is `storage.snapOpensOk`. -/
opaque dirReadOk (ss : Loc) : Prop

/-- The record that the ghost map `γd` tracks the snapshot directory at the paths `p` (opaque; see
`snapDirIs`). -/
opaque snapDirIsRO (p : w64 → GoString) (γd : GName) : IProp GF

/-- **The ghost map `γd` tracks the snapshot directory at the paths `p`** (persistent; restart S6a,
M1, approved by the user 2026-11-13 via etcd-grove-81; see the file header): made only from the
directory's right `snapDirOwn p`, once (`snapDirOwn_claim`). The directory invariant holds it
(`snapDirInv`, `Proof/.../rafthttp/Net.lean`), so that the invariant the snapshot axioms
(`SaveDBFrom`, `Release`) take is the one invariant of its files. -/
def snapDirIs (p : w64 → GoString) (γd : GName) : IProp GF := iprop(□ snapDirIsRO p γd)

instance snapDirIs_persistent (p : w64 → GoString) (γd : GName) :
    Persistent (snapDirIs (GF := GF) p γd) := by
  unfold snapDirIs; infer_instance

/-- **The program's right to the snapshot directory at the paths `p`** (restart S6a, M1; approved by
the user 2026-11-13 via etcd-grove-81; a named premise about the program's environment, which
`bootOk` gives at the first start at `p = snapDBPathOf cfg.DataDir`, and `bootOkR` never gives).
The environment assumption: at the first start the snapshot directory holds no `.snap.db` file, and
nothing outside the server's snapshotters writes `.snap.db` files there (etcd's own
`bootstrapSnapshot` removes only `tmp*` and `*.snap` files, `bootstrap.go:210-252`, so a `.snap.db`
file kept from an earlier data directory would stay). Read as: the one ghost map that tracks the
directory's files from empty may be named, once, by whoever holds the right (`snapDirOwn_claim`,
consumed by `snapDir_init`). Not exclusive by a law: what makes it one per directory is that the
environment gives it once. -/
def snapDirOwn (p : w64 → GoString) : IProp GF := iprop(∀ γd : GName, |==> snapDirIs p γd)

/-- The directory's right names its ghost map (see `snapDirOwn`). -/
theorem snapDirOwn_claim (p : w64 → GoString) (γd : GName) :
    snapDirOwn (GF := GF) p ⊢ |==> snapDirIs p γd := by
  unfold snapDirOwn
  iintro H
  iapply H

instance isSnapshotter_persistent (ss : Loc) : Persistent (isSnapshotter (GF := GF) ss) := by
  unfold isSnapshotter; infer_instance

/-- `m`'s fields, read-only (opaque; see the file header). -/
opaque msgRO (m ml : Loc) (rc : GoInterface) : IProp GF

/-- **`m` is a `*snap.Message` of the raft message `ml` and the reader `rc`** (persistent; see the
file header). -/
def msgIs (m ml : Loc) (rc : GoInterface) : IProp GF := iprop(□ msgRO m ml rc)

instance msgIs_persistent (m ml : Loc) (rc : GoInterface) :
    Persistent (msgIs (GF := GF) m ml rc) := by
  unfold msgIs; infer_instance

/-- `m`'s `closeC` field, read-only (opaque; see the file header). -/
opaque msgCloseRO (m c : Loc) : IProp GF

/-- **`m`'s `closeC` is `c`** (persistent; D22 S-h; see the file header). -/
def msgCloseC (m c : Loc) : IProp GF := iprop(□ msgCloseRO m c)

instance msgCloseC_persistent (m c : Loc) : Persistent (msgCloseC (GF := GF) m c) := by
  unfold msgCloseC; infer_instance

end defs

end snap
end EtcdGrove
end Perennial
