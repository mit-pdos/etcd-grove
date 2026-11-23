/-
**The snapshotter** (`etcdserver/api/snap`, names only; D22 S-f, 2026-10-19): the vocabulary of
its trust-boundary specs. Lean-first (no Rocq counterpart).

* `isSnapshotter ss sd` (persistent): `ss` is a `*snap.Snapshotter` of the directory `sd`
  (`snap.New(lg, dir)`: its fields, the logger and the snapshot directory, set once and read-only
  after): the persistent cells of its `lg` and `dir` fields (`snapLgAddr`, `snapDirAddr`), and of its
  `fsyncDir` field, `fsyncSnapDir` (`snapshotterRO`; opaque until claim #34, 2026-11-23). (wal-link, 2026-11-19, approved by the user via
  etcd-grove-03: the directory is the `dir` field's cell, so it is fixed per execution by the heap;
  until then a pure opaque function of the location, `snapDBPath ss`, which the bootstrap contracts
  pinned per run: `notes/snapdir-crossworld.md`.)
* `snapDBPath sd i` (a definition): the path of the database snapshot of index `i` in the directory
  `sd` (`ss.dbFilePath(i)`: `<sd>/<i as 16 hex digits>.snap.db`; Go's parameter is named `id`, but it
  is the snapshot's index, not a member id). `DBFilePath` returns it
  (`Spec/.../snap/Snapshotter__DBFilePath.lean`); the transport's `SaveDBFrom` writes the file there
  (D22 S-i).
* `snapDirOwn p` and `snapDirIs p γd` (restart S6a, M1; approved by the user 2026-11-13 via
  etcd-grove-81): the environment's one-time right to the snapshot directory whose files are at the
  paths `p` (`bootOk`, the first start: the directory holds no `.snap.db` file, and nothing outside
  the server's snapshotters writes `.snap.db` files there), and the persistent record, made once from
  it, of the ghost map `γd` that tracks those files (`snapDirInv`, `Proof/.../rafthttp/Net.lean`).
* `msgIs m ml rc` (persistent; D22 S-i): `m` is a `*snap.Message` (`snap.NewMessage(ml, rc,
  size)`: the raft message `ml`, the reader `rc` wrapped in an exact-size reader, the total size
  and the one-slot `closeC` channel), its fields read-only for good (`NewMessage` writes them
  once; `CloseWithError` reads the reader and sends on `closeC`, `CloseNotify` reads `closeC`). An
  predicate of the fields (`msgRO`; opaque until 2026-11-19, when `snap.Message`'s
  `CloseNotify` and `CloseWithError` were translated with their bodies). `NewMessage`'s spec makes it (D22 S-h), and only it, of a reader whose `Close` returns
  (`io.rcCloseOk`; sweep repairs 1, S1) and a size in its premise's range (S2); the transport's
  `SendSnapshot` takes it.
* `msgCloseC m c` (persistent; D22 S-h): `m`'s `closeC` is the channel `c` (`NewMessage`'s
  `make(chan bool, 1)`, read by `CloseNotify`): the field, read-only (`msgCloseRO`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap
public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.etcd.server.v3.config.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Hex16
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace snap

open Iris Iris.BI

/-- **The name of the database snapshot of index `i`** (`fmt.Sprintf("%016x.snap.db", id)`,
`server/etcdserver/api/snap/db.go:118`; wal-link, 2026-11-19). -/
def snapDBName (i : w64) : GoString := WalFs.hex16 (uint.nat i) ++ go!".snap.db"

/-- **The path of the database snapshot of index `i` in the snapshot directory `sd`** (restart
S6a, approved by the user 2026-11-13 via etcd-grove-81, as `snapDBPathOf dd`, opaque; wal-link,
2026-11-19, decided by etcd-grove-03, option B1: a definition; wal-link, 2026-11-19, approved by the
user via etcd-grove-03: over the directory string, `snapDBPathOf dd` gone for `snapDBPath (snapDirOf
dd)`, and the snapshotter's own opaque `snapDBPath ss` gone: `notes/snapdir-crossworld.md`):
`<sd>/<i as 16 hex digits>.snap.db`, the name `snapDBName i` in `sd`. `i` is the snapshot's index
(Go's `dbFilePath(id)` names it `id`). For a member, `sd` is `config.snapDirOf cfg.DataDir`
(`<dd>/member/snap`, where the backend's file, `config.backendPathOf dd`, is the name `db`): the
bootstrap contracts (`bootOk`, `bootOkR`) give `isSnapshotter ss (config.snapDirOf cfg.DataDir)`, so
that two incarnations of a member over one data directory write their snapshots to the same files.
Go: `bootstrapSnapshot` returns `snap.New(cfg.Logger, cfg.SnapDir())`
(`server/etcdserver/bootstrap.go:252`); `SnapDir()` is `filepath.Join(c.MemberDir(), "snap")` and
`MemberDir()` is `datadir.ToMemberDir(c.DataDir)` (`server/config/config.go:300,309`);
`dbFilePath(id)` is `filepath.Join(s.dir, fmt.Sprintf("%016x.snap.db", id))`
(`server/etcdserver/api/snap/db.go:117-119`), and `s.dir` is written only by `New`
(`snapshotter.go:34-40`). `filepath.Join` is lexical and cleans; a snapshotter's `s.dir` is some
`cfg.SnapDir()` (`isSnapshotter`), already clean and not ending in `/` (it ends in `snap`), and the
name is clean, so the join is `s.dir ++ "/" ++ name` (the Go test
`examples/etcd/snappaths/snappaths_test.go`). The equation is about strings; that equal path strings
name the same file (no change of working directory between incarnations under a relative `DataDir`,
no symbolic link or other alias of the directory, and a restart under the same `DataDir` string) is
the file-system model's assumption that a path string names one file, as for `config.backendPathOf`
and `backend.bPath`. -/
def snapDBPath (sd : GoString) (i : w64) : GoString := sd ++ slashB :: snapDBName i

/-- The address of the snapshotter `ss`'s logger field (`s.lg`; `snap.Snapshotter` is an
axiomatized type, so the field is named, not modeled). -/
abbrev snapLgAddr [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] (ss : Loc) : Loc :=
  structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter go!"lg" ss

/-- The address of the snapshotter `ss`'s directory field (`s.dir`, written only by `snap.New`,
`snapshotter.go:34-40`, read by `dbFilePath`, `DBFilePath`, `SaveDBFrom`, `ReleaseSnapDBs`;
wal-link, 2026-11-19). -/
abbrev snapDirAddr [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] (ss : Loc) : Loc :=
  structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter go!"dir" ss

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`ss`'s remaining field, read-only** (claim #34, 2026-11-23, approved by the owner via the
coordinator, option (a): defined, until then opaque): the `fsyncDir` field holds the package function
`fsyncSnapDir`, the value `snap.New` stores (`snapshotter.go:34-43`: `&Snapshotter{lg, dir, fsyncDir:
fsyncSnapDir}`) and `SaveDBFrom` calls on the directory (`s.fsyncDir(s.dir)`, `db.go`). Nothing writes the
field after `New` (it is unexported, and the package writes it nowhere else). -/
def snapshotterRO (ss : Loc) : IProp GF :=
  iprop(structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter
      go!"fsyncDir" ss ↦□
    functions _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.fsyncSnapDir [])

instance snapshotterRO_persistent (ss : Loc) : Persistent (snapshotterRO (GF := GF) ss) := by
  unfold snapshotterRO; infer_instance

/-- **`ss` is a snapshotter of the directory `sd`** (persistent; see the file header): its `dir`
field `sd` (wal-link, 2026-11-19), a snapshot directory of etcd's (`cfg.SnapDir()` of some data
directory: `bootstrapSnapshot`'s `snap.New(cfg.Logger, cfg.SnapDir())`, the only snapshotter etcd
makes, `server/etcdserver/bootstrap.go:252`), its logger a zap logger (`zapLoggerOk`; premise fixes 6:
`SaveDBFrom` logs through it; `snap.New(lg, dir)` stores `lg`, nil replaced by `zap.NewNop()`). -/
def isSnapshotter (ss : Loc) (sd : GoString) : IProp GF :=
  iprop(□ snapshotterRO ss ∗ snapDirAddr ss ↦□ sd ∗ ⌜∃ dd, sd = config.snapDirOf dd⌝ ∗
    ∃ lg : Loc, snapLgAddr ss ↦□ lg ∗ zapLoggerOk lg)

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
`bootOk` gives at the first start at `p = snapDBPath (config.snapDirOf cfg.DataDir)`, and `bootOkR` never gives).
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

instance isSnapshotter_persistent (ss : Loc) (sd : GoString) :
    Persistent (isSnapshotter (GF := GF) ss sd) := by
  unfold isSnapshotter; infer_instance

/-- `m`'s `closeC` field, read-only (see the file header; opaque until 2026-11-19). -/
def msgCloseRO (m c : Loc) : IProp GF :=
  iprop(structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message go!"closeC" m ↦□ c)

/-- **`m`'s `closeC` is `c`** (persistent; D22 S-h; see the file header). -/
def msgCloseC (m c : Loc) : IProp GF := iprop(□ msgCloseRO m c)

instance msgCloseC_persistent (m c : Loc) : Persistent (msgCloseC (GF := GF) m c) := by
  unfold msgCloseC; infer_instance

end defs

section msgDefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `m`'s fields, read-only (see the file header; opaque until 2026-11-19, when `CloseWithError` was
translated and proved): the raft message `ml`; the total size, not negative; the reader, an
exact-size wrapper whose complete streams are `rc`'s and whose `Close` returns; `closeC`, a
channel of booleans whose receives carry nothing (`isChanBag` at `True`); and (prove-grpcsmall,
2026-11-20) the raft message `ml` itself, read-only at some content (`NewMessage`'s read-only
argument, which the promoted getters read). `NewMessage` makes it
(its trust-boundary axiom, `Proof/.../snap/NewMessage.lean`). -/
def msgRO (m ml : Loc) (rc : GoInterface) : IProp GF :=
  iprop(structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message go!"Message" m ↦□ ml ∗
    (∃ tsz : w64, structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message
      go!"TotalSize" m ↦□ tsz ∗ ⌜0 ≤ sint.Z tsz⌝) ∗
    (∃ (rd : GoInterface) (ri : GoInterfaceOk),
      structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message
        go!"ReadCloser" m ↦□ rd ∗ ⌜rd = GoInterface.ok ri⌝ ∗
      □ (∀ Φ : List w8 → Prop, backend.readerStreams rc Φ -∗ backend.readerStreams rd Φ) ∗
      □ {{ (True : IProp GF) }}
          (App (Val #(methods ri.ty go!"Close" ri.v)) (Val #()))
        {{ (err : GoInterface), RET #err; True }}) ∗
    (∃ (c : Loc) (γc : ChanNames),
      structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message go!"closeC" m ↦□ c ∗
      isChanBag γc c (V := Bool) (fun _ => iprop(True))) ∗
    (∃ st : MsgSt, msgOwn ml DFrac.discard st))

/-- **`m` is a `*snap.Message` of the raft message `ml` and the reader `rc`** (persistent; see the
file header). -/
def msgIs (m ml : Loc) (rc : GoInterface) : IProp GF := iprop(□ msgRO m ml rc)

instance msgIs_persistent (m ml : Loc) (rc : GoInterface) :
    Persistent (msgIs (GF := GF) m ml rc) := by
  unfold msgIs; infer_instance

end msgDefs

end snap
end EtcdGrove
end Perennial
