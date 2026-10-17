/-
`snap.Snapshotter`'s pending-apply marks (`server/etcdserver/api/snap/`), as etcd PR #22046
adds them (branch `pr-verify/etcd-22046` only). Lean-first (no Rocq counterpart).

**The marks.** `pendingDBs` (a `map[uint64]struct{}`, the field written once, by `New`) holds the
indices of the snapshot database files saved on receipt (`SaveDBFrom`) and not yet consumed by
the apply path (`OpenSnapshotBackend`, through `ReleaseDBSnapshot`); `ReleaseSnapDBs` skips them.
The mutex `pendingDBsMu` guards the map's contents. Its lock invariant (`snapPendingR`) holds
the contents `M` and half of a ghost variable `γ` at `M`; the other half is the library's
abstract state (`snapPending γ M`), which the clients share (the receiver, the raft loop and the
apply loop, through an invariant of their own). So each of `markPendingDB`, `isPendingDB` and
`ReleaseDBSnapshot` is logically atomic: its linearization point is inside the critical section,
where it updates (or reads) both halves.

**The snapshotter** (`isSnapshotter s γ dir`, persistent): the read-only fields `lg`
(non-nil), `dir`, `fsyncDir` (the function `fsyncSnapDir`, as `New` sets it; only tests change
it) and `pendingDBs`, and the mutex with its lock invariant.

**Removing files** (`ReleaseSnapDBs`). There is no file-system model; `os.Remove(p)`'s
trust-boundary spec takes an abstract right `fs.removable p` (no one relies on `p`'s existence),
which nothing here produces: `ReleaseSnapDBs`'s caller gives it, through a hook
(`snapRemoveHook`) that `ReleaseSnapDBs` runs at the linearization point of its `isPendingDB`
check of each file it would remove. `fs.join` is `filepath.Join` (abstract).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvSnapshotBackend
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap
public import Perennial.Proof.sync
public import Perennial.Ghost.GhostVar
public import Perennial.ProgramLogic.AtomicFupd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&s.pendingDBsMu`. -/
abbrev snapMuAddr (s : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter go!"pendingDBsMu" s

/-- `&s.pendingDBs`. -/
abbrev snapPendingAddr (s : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter go!"pendingDBs" s

/-- `&s.dir`. -/
abbrev snapDirAddr (s : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter go!"dir" s

/-- `&s.fsyncDir`. -/
abbrev snapFsyncAddr (s : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter go!"fsyncDir" s

/-- `&s.lg`. -/
abbrev snapLgAddr (s : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter go!"lg" s

end addrs

/-- `filepath.Join(xs...)` (abstract). -/
opaque fs.join : List GoString → GoString

/-- `filepath.Base(p)` (abstract). -/
opaque fs.base : GoString → GoString

/-- `strings.TrimSuffix(s, suffix)` (abstract). -/
opaque str.trimSuffix : GoString → GoString → GoString

/-- `strconv.ParseUint(s, base, bitSize)` when it returns a nil error (abstract). -/
opaque str.parseUint : GoString → w64 → w64 → Option w64

/-- The index `ReleaseSnapDBs` parses from a directory entry `name`
(`strconv.ParseUint(strings.TrimSuffix(filepath.Base(name), ".snap.db"), 16, 64)`), if the parse
succeeds. -/
def snapDBIndexOf (name : GoString) : Option w64 :=
  str.parseUint (str.trimSuffix (fs.base name) go!".snap.db") (W64 16) (W64 64)

section fsdefs
variable {GF : BundledGFunctors}

/-- The right to remove the file `p`: no one relies on its existence (abstract; see the file
header). -/
opaque fs.removable (p : GoString) : IProp GF := iprop(True)

/-- The open file `f` is named `p` (`f.Name()`; abstract, what `os.CreateTemp` returns). -/
opaque fs.fileName (f : Loc) (p : GoString) : IProp GF := iprop(True)


end fsdefs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `r` is an `io.Reader` that `io.Copy` may read from to its end (abstract: what `SaveDBFrom`'s
caller, the snapshot receiver, gives of the HTTP request body). -/
opaque ioReader (r : GoInterface) : IProp GF := iprop(True)

/-- **The marks' abstract state**: the pending set is (the domain of) `M`. Half of `γ`; the
other half is in the lock invariant. -/
abbrev snapPending (γ : GName) (M : GMap w64 Unit) : IProp GF := ghostVar γ (1 : Qp).half M

/-- **The lock invariant** of `s.pendingDBsMu`: the map `mref`'s contents `M`, with the other
half of `γ` at `M`. -/
def snapPendingR (γ : GName) (mref : Loc) : IProp GF :=
  iprop(∃ M : GMap w64 Unit, mref ↦$ M ∗ ghostVar γ (1 : Qp).half M)

/-- **The snapshotter `s`** (persistent; see the file header): its read-only fields (`lg`
non-nil, `dir`, `pendingDBs` the map `mref`) and the mutex guarding the map. -/
def isSnapshotter (s : Loc) (γ : GName) (dir : GoString) : IProp GF :=
  iprop(∃ (mref lg : Loc),
    typedPointsto (snapPendingAddr s) mref DFrac.discard ∗
    typedPointsto (snapLgAddr s) lg DFrac.discard ∗ ⌜lg ≠ null⌝ ∗
    typedPointsto (snapDirAddr s) dir DFrac.discard ∗
    typedPointsto (snapFsyncAddr s)
      (functions go_etcd_io.etcd.server.v3.etcdserver.api.snap.fsyncSnapDir []) DFrac.discard ∗
    sync.isMutex (snapMuAddr s) (snapPendingR γ mref))

instance isSnapshotter_persistent (s : Loc) (γ : GName) (dir : GoString) :
    Persistent (isSnapshotter (GF := GF) s γ dir) := by
  unfold isSnapshotter; infer_instance

/-- **What `ReleaseSnapDBs(snap)` takes from its caller** (persistent): for every file `name` of
the snapshotter's directory `dir` whose parsed index `i` (`snapDBIndexOf name`) is below the snapshot's (`idx`), an
atomic look at the pending set `M` (the linearization point of the `isPendingDB(i)` check) that,
if `i` is not pending then, gives the right to remove `dir/name`. -/
def snapRemoveHook (γ : GName) (dir : GoString) (idx : w64) : IProp GF :=
  iprop(□ ∀ (name : GoString) (i : w64), ⌜snapDBIndexOf name = some i⌝ -∗ ⌜uint.Z i < uint.Z idx⌝ -∗
    |={⊤,∅}=> ∃ M, snapPending γ M ∗
      (snapPending γ M ={∅,⊤}=∗ (⌜M !! i = none⌝ -∗ fs.removable (fs.join [dir, name]))))

instance snapRemoveHook_persistent (γ : GName) (dir : GoString) (idx : w64) :
    Persistent (snapRemoveHook (GF := GF) γ dir idx) := by
  unfold snapRemoveHook; infer_instance

end defs

end EtcdGrove
end Perennial
