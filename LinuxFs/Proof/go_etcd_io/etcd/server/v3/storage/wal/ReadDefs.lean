/-
The read-phase handles of the WAL over `fsExt` (W3/W5 of `notes/wal-fsext-plan.md`): what `Open`
returns and `ReadAll` takes (`walOpeningF`), what `OpenForRead` returns (`walReadOnlyF`), and what a
failed `ReadAll` leaves (`walReadFailedF`), the program-level counterparts of the ghost
`walOpening`/`walReadFailed` (`Ghost.lean`), as `walOpenWF` (`Handle.lean`) is of `walOpenW`. The
three are sealed: the specs that mention them (`LinuxFs/Spec/.../wal/{Open,OpenForRead,WAL__ReadAll}.lean`)
do not depend on their bodies.

**The bodies** (2026-11-13, branch `wal-read2`; the plan's W3/W5 log, "Decisions" 2):
* `walOpenedFile write dir b i fr lf`: a file `openWALFiles` opened, the name `b` of `dir`, inode
  `i`: its `*os.File` (fd whole, `O_RDWR` in write mode, `O_RDONLY` in read mode, `O_CLOEXEC`
  added by `os.OpenFile`), offset 0, its `fileutil.FileReader` (`*fileReader{f}`) and its lock
  (`TryLockFile`'s `*LockedFile` in write mode, nil in read mode).
* `walFileS f fd i g r`: the stream state of such a file read as the segment `g` (`DecFile.S`, what
  the `os.File`-as-`io.Reader` bridge takes, `ReadBridge.lean`): `r` a prefix of the bytes, the
  file, the fd, the offset `|r|`, and the program's halves of `g`'s `OsMeta` and bytes. With them the bytes the decoder reads
  (`DecFile.bs`, the page cache's values of `g.bs`) cannot change during the read.
* `walReadTie dir write s j fs lfs`: the decoder's files are the WAL's segments from the opened one on
  (at least one: `selectWALFiles` fails with `ErrFileNotFound` on none; in write mode the last one at the
  claim's last `.wal` name, so the handle's last file is the WAL's tail: `Close.specOpening`'s `wp_idleFsync`),
  each read through `walFileS`; the program's half of the WAL directory's claim (`WalDirClaim`), so
  that the directory's names cannot change either (no atomic readdir needed), the segments' names the
  claim's `.wal` names from some position on (`(walNames hj.cur).drop kk = gs.map name`: with the
  invariant's `WalAbsD.names`, the segments are the layout's from `kk` on, `walInvBody_readState`); in write mode each
  lock is `fileutil.lockedFile` of its file. And what the pin returns for the put-back
  (`walInvBody_unpin`, `OpenUnpin.lean`; 2026-11-14): the record of what is out (`walOutFrag`: the
  segments' inodes, the directory's claim key, in write mode the pipeline names of `dir`), the holder's
  empty half of the tails' authority (`walTailsFrag ∅`: `ReadAll` registers the tail with it), the
  WAL's key (`walDirKey`), the segments' inodes distinct and each of its bytes' size.
* `walReadH write w dir s`: the struct's fields as `openAtIndex` leaves them: `lg`, `dir`, `start`,
  the decoder (`ownDecoder` live at offset 0, CRC 0, over `fs`, its readers' errors `IoE` none of them
  `nil`: `ReadAll`'s loop), `locks`, `readClose` (`nil` in write
  mode), the pipeline (write mode: `walPipeH fp dir j 0`, at the inode `j` of the directory whose claim
  `walReadTie` holds; read mode: `nil`), the zero fields
  (`encoder`, `state`, `metadata`, `enti`, `snapi`, `unsafeNoSync`), the mutex, the decoder's
  environment.

**Where the program's halves come from** (decision 2): `Open`, holding the lock token
(`walUnlockedTok`: the parking flag `true`, so nothing is out), takes them out of `walInv`'s
`walParked` (`Inv.lean`) and sets the flag to `false` (`walUnlockedTok_lock`; the handles hold
`walLockedTok`); `ReadAll` puts them back when it returns the write handle (all but the tail's,
which `walTailW` keeps), or `Close`/the failure does. The `os.File` reader bridge proving `decFile` of a `walFileS` stream: `ReadBridge.lean`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- The open flags of `openWALFiles` (`os.O_RDWR` in write mode, `os.O_RDONLY` in read mode) as
`os.OpenFile` passes them (`O_CLOEXEC` added). -/
def walReadFlag (write : Bool) : w64 := (if write then W64 2 else W64 0) ||| W64 0x80000

/-- See the file header. -/
def walOpenedFile (write : Bool) (dir b : GoString) (i : Ino) (fr : GoInterfaceOk) (lf : Loc) :
    IProp GF :=
  iprop(∃ (f : Loc) (fd : w64) (rl : Loc),
    os.ownFile f fd (child dir b) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (openFd i (walReadFlag write)) ∗
    os.ownOff f (W64 0) ∗ ⌜0 ≤ fd.toInt⌝ ∗
    ⌜GoInterface.ok fr = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl⌝ ∗
    rl ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f ∗
    (if write then fileutil.lockedFile lf f else ⌜lf = null⌝))

/-- See the file header. -/
def walFileS (f : Loc) (fd : w64) (name : GoString) (fl : OsFd) (g : SegG) (r : List w8) :
    IProp GF :=
  iprop(⌜r <+: g.bs.map Prod.fst⌝ ∗
    os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) fl ∗ os.ownOff f (W64 r.length) ∗
    osMeta g.ino (DFrac.own (1 : Qp).half) g.om ∗ osBytes g.ino 0 (DFrac.own (1 : Qp).half) g.bs)

/-- See the file header. -/
def walReadTie (dir : GoString) (write : Bool) (s : w64 × w64) (j : Ino) (fs : List (DecFile GF))
    (lfs : List Loc) : IProp GF :=
  iprop(∃ (X : List GoString) (hj : NamesH) (gs : List SegG) (fls : List Loc),
    osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
    walOutFrag (W := W) ⟨gs.map (·.ino), [(j, .except X)], if write then [dir] else []⟩ ∗
    (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗ walDirKey (W := W) dir j X ∗
    ⌜gs ≠ [] ∧ (gs.map (·.ino)).Nodup ∧ (∀ g ∈ gs, g.om.size = g.bs.length) ∧
      (∀ g, gs.head? = some g → ∀ sq ix, g.name = walFileName sq ix → ix < 2 ^ 64 → ix ≤ uint.nat s.1) ∧
      (write = true → ∀ g, gs.getLast? = some g → (walNames hj.cur).getLast? = some g.name) ∧
      ∃ kk, (walNames hj.cur).drop kk = gs.map (·.name)⌝ ∗
    ⌜fs.length = gs.length ∧ lfs.length = gs.length ∧ fls.length = gs.length ∧
      ∀ (k : Nat) (F : DecFile GF) (g : SegG), fs[k]? = some F → gs[k]? = some g →
        F.bs = g.bs.map (·.1) ∧ hj.cur !! g.name = some (.file g.ino) ∧
        ∃ (f : Loc) (fd : w64), fls[k]? = some f ∧
          F.S = walFileS f fd (child dir g.name) (openFd g.ino (walReadFlag write)) g⌝ ∗
    [∗list] k ↦ lf ∈ lfs, if write then fileutil.lockedFile lf (fls.getD k null) else ⌜lf = null⌝)

/-- **The fields of a handle `Open` made** (draft, see the file header): the logger, the
directory, the start snapshot `s`. -/
def walOpenIn (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  iprop(∃ (lg sp : Loc),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"start" w ↦ sp ∗
    walSnapIdTerm sp s)

/-- See the file header. -/
def walReadH (write : Bool) (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  iprop(walOpenIn w dir s ∗
    ∃ (dec : Loc) (IoE : GoInterface → Prop) (eof ueof : GoInterface) (fs : List (DecFile GF))
      (locks : GoSlice) (lfs : List Loc) (fp : Loc) (rc : GoFunc) (j : Ino),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"decoder" w ↦
      interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.decoder.ty) #dec ∗
    ownDecoder dec IoE eof fs 0 0#32 true ∗ (decEnv IoE eof ueof ∗ ⌜¬ IoE GoInterface.nil⌝) ∗
    walReadTie dir write s j fs lfs ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
    locks ↦* lfs ∗ ownSliceCap Loc locks (DFrac.own 1) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"readClose" w ↦ rc ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗
    (if write then iprop(⌜rc = zero_val GoFunc⌝ ∗ walPipeH fp dir j 0) else ⌜fp = null⌝) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ (null : Loc) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ (null : Loc) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"metadata" w ↦ slice.nil ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ W64 0 ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ W64 0 ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
      (BI.pure True : IProp GF) ∗
    encEnv ∗ walCrcTable)

/-- **`w` is the WAL `Open` opened in `dir` at the snapshot `s`, not yet read** (the specs' handle;
sealed): the ghost handle, `openAtIndex`'s fields in write mode, `w.dirFile`
(`fileutil.OpenDir(dir)`: a shared directory fd on the WAL directory, not read), and the client's half
of the call permission (the pipeline holds the other; `ReadAll` moves it into the write handle's
`walDirH`: `notes/specs-only/ledger.md`, 2026-11-14, "the call permission counted twice"). -/
@[no_expose] def walOpeningF (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  iprop(walOpening (W := W) w dir s ∗ walReadH true w dir s ∗ osCallPerm (1 : Qp).half ∗
    ∃ (df : Loc) (dfd : w64) (j : Ino),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
    os.ownFile df dfd dir (DFrac.own 1) ∗ osDirFdS dfd j .idle)

/-- **`w` is the WAL `OpenForRead` opened in `dir` at `s`** (read mode, sealed): the lock token,
taken (`walLockedTok`: the reader holds the program's halves of the files as `Open`'s does),
`openAtIndex`'s fields in read mode, no `dirFile`. -/
@[no_expose] def walReadOnlyF (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  iprop(walLockedTok (W := W) ∗ walReadH false w dir s ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ (null : Loc))

/-- **`w`'s `ReadAll` in `dir` failed** (the specs' handle; sealed): only `Close` accepts it.
Draft body: the ghost handle and the logger and directory fields (`Close`'s spec, W10, adds what it
reads: the locks, the pipeline, `dirFile`; the program's halves go back to `walInv` at the failure). -/
@[no_expose] def walReadFailedF (w : Loc) (dir : GoString) : IProp GF :=
  iprop(walReadFailed (W := W) w dir ∗ ∃ lg : Loc,
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir)

end handle

end WalFs
end EtcdGrove
end Perennial
