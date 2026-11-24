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
* `snapDirOwn p` (restart S6a, M1; approved by the user 2026-11-13 via etcd-grove-81; claim #34,
  2026-11-23, approved by the owner via the coordinator: a file-system claim): the claim on every name
  of the snapshot directory whose files are at the paths `p` but `db` and the canonical `.snap.db`
  names (`snapDirNames`), which `bootstrapSnapshot` carves and the directory's invariant holds
  (`snapDirInv`, `Proof/.../rafthttp/Net.lean`). Until then `snapDirIs p γd` over the opaque
  `snapDirIsRO`, a right only `bootOk` gave.
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

/-- A map injective on a duplicate-free list keeps it duplicate-free. -/
theorem nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α),
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hf, hl => by
    have hl' := List.nodup_cons.1 hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on f l (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy)) hl'.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
    have := hf b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) hfb
    subst this
    exact hl'.1 hb

/-- A list of every `w64`, once, exists (`(List.range (2 ^ 64)).map (BitVec.ofNat 64)`). -/
theorem allW64_exists : ∃ l : List w64, (∀ i, i ∈ l) ∧ l.Nodup := by
  refine ⟨(List.range (2 ^ 64)).map (fun n => BitVec.ofNat 64 n), fun i => ?_, ?_⟩
  · exact List.mem_map.2 ⟨i.toNat, List.mem_range.2 i.isLt, BitVec.ofNat_toNat _ _⟩
  refine nodup_map_on _ _ ?_ List.nodup_range
  intro a ha b hb hab
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  have := congrArg BitVec.toNat hab
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  exact this

/-- **Every `w64`, once** (`bootSnap.mem_allW64`, `bootSnap.allW64_nodup`): a list with each `w64`
exactly once, chosen (its order is irrelevant: `snapDirNames` is used as a set of names). Not the
literal `(List.range (2 ^ 64)).map _`: a definition the kernel can unfold made it unfold the
`2 ^ 64`-element list when checking `bootSnap.snapDir_carve` (claim #34, 2026-11-24); the kernel
cannot unfold a choice. -/
def allW64 : List w64 := Classical.choose allW64_exists

/-- **The names of a snapshot directory that are not its right's** (`snapDirOwn`; claim #34,
2026-11-23): the backend's database file `db` (`config.backendPathOf`) and every index's database
snapshot `snapDBName i`. -/
def snapDirNames : List GoString := go!"db" :: allW64.map snapDBName

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

/-- **The program's right to the snapshot directory at the paths `p`** (restart S6a, M1, approved by
the user 2026-11-13 via etcd-grove-81; claim #34, 2026-11-23, approved by the owner via the coordinator:
a file-system claim, until then `∀ γd, |==> snapDirIs p γd` over the opaque `snapDirIsRO`, which `bootOk`
alone gave). `p` is the paths of a directory `sd`'s database snapshots (`p = snapDBPath sd`), and the right
is the file extension's whole claim on every name of `sd` but those `snapDirNames` lists (`db`, the
backend's file, and every index's `<16 hex>.snap.db`, whose claims go to the backend and to `snapFreeAll`),
with shares of `sd`'s path and of its root's call permission, at the program's file-extension instances.
`bootstrapSnapshot` carves it out of the snapshot directory it makes (`bootSnap.snapDir_carve`), and
`snapDir_init` puts it in the directory's invariant for good (`snapDirInv`, `Proof/.../rafthttp/Net.lean`).

What it makes true. The claims of a directory are disjoint (the extension's `NamesCoh.disj`), so while the
invariant holds this claim no one else holds a claim on any name of `sd` outside `snapDirNames`: no
proof can have created, or can create, a file under a non-canonical `.snap.db` name (`5.snap.db`, 19
digits, uppercase hex) or a `tmp*` name there. So `ReleaseSnapDBs`'s removal of such entries and
`SaveDBFrom`'s temporary file are steps on names only the invariant claims; and a second invariant over
`sd` would need a second copy of the claim, so the directory's invariant is one per directory (M1). The
claim's history `h` is free: the axioms that act on these names inside the invariant update it. -/
def snapDirOwn (p : w64 → GoString) : IProp GF :=
  backend.onFs iprop(∃ (sd : GoString) (R : Fs.Roots) (J : Fs.Ino) (q qc : Qp) (h : Fs.NamesH),
    ⌜p = snapDBPath sd⌝ ∗ Fs.osInv ∗ Fs.osSharedInv R ∗ Fs.osPathS R sd (DFrac.own q) J ∗
    Fs.osCallPerm (Fs.callKey R sd) qc ∗ Fs.osNames J (.except snapDirNames) (DFrac.own 1) h)

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
