/-
The read-phase handles of the WAL over `fsExt` (W3/W5 of `notes/wal-fsext-plan.md`): what `Open`
returns and `ReadAll` takes (`walOpeningF`), what `OpenForRead` returns (`walReadOnlyF`), and what a
failed `ReadAll` leaves (`walReadFailedF`, its body `walFailH`: unit `closefailed`), the program-level counterparts of the ghost
`walOpening`/`walReadFailed` (`Ghost.lean`), as `walOpenWF` (`Handle.lean`) is of `walOpenW`. The
three are sealed: the specs that mention them (`Spec/.../wal/{Open,OpenForRead,WAL__ReadAll}.lean`)
do not depend on their bodies.

**The bodies** (2026-11-13, branch `wal-read2`; the plan's W3/W5 log, "Decisions" 2):
* `walOpenedFile write dir b i fr lf`: a file `openWALFiles` opened, the name `b` of `dir`, inode
  `i`: its `*os.File` (fd whole, `O_RDWR` in write mode, `O_RDONLY` in read mode, `O_CLOEXEC`
  added by `os.OpenFile`; in write mode locked, `walSegFd`, with its locks, `fdLocks`), offset 0, its `fileutil.FileReader` (`*fileReader{f}`) and its lock
  (`TryLockFile`'s `*LockedFile` in write mode, nil in read mode).
* `walFileS f fd i g r`: the stream state of such a file read as the segment `g` (`DecFile.S`, what
  the `os.File`-as-`io.Reader` bridge takes, `ReadBridge.lean`): `r` a prefix of the bytes, the
  file, the fd (non-negative: `Seek` needs it) and its locks (`fdLocks`), the offset `|r|`, and the program's halves of `g`'s `OsMeta` and bytes. With them the bytes the decoder reads
  (`DecFile.bs`, the page cache's values of `g.bs`) cannot change during the read.
* `walReadTie dir write s j fs lfs`: the decoder's files are the WAL's segments from the opened one on
  (at least one: `selectWALFiles` fails with `ErrFileNotFound` on none; in write mode the last one at the
  claim's last `.wal` name, so the handle's last file is the WAL's tail: `Close.spec` (state `opening`)'s `wp_idleFsync`),
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

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandlePend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

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

/-- The description of a segment file `openWALFiles` opened: readable, writable in write mode
(`O_RDWR`; `O_RDONLY` in read mode), its locks `lo`/`lk` (2026-11-15, the lock semantics: in write mode
`TryLockFile`'s exclusive lock, whose token and kind `fdLocks` holds). -/
def walSegFd (write : Bool) (lo lk : Option Bool) (i : Ino) : OsFd := ⟨i, true, write, lo, lk⟩

/-- See the file header. -/
def walOpenedFile (write : Bool) (dir b : GoString) (i : Ino) (fr : GoInterfaceOk) (lf : Loc) :
    IProp GF :=
  iprop(∃ (f : Loc) (fd : w64) (rl : Loc) (lo lk : Option Bool),
    os.ownFile f fd (child dir b) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (walSegFd write lo lk i) ∗
    fdLocksW fd (walSegFd write lo lk i) ∗
    os.ownOff f (W64 0) ∗ ⌜0 ≤ fd.toInt⌝ ∗
    ⌜GoInterface.ok fr = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl⌝ ∗
    rl ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f ∗
    (if write then fileutil.lockedFile lf f else ⌜lf = null⌝))

/-- See the file header. -/
def walFileS (f : Loc) (fd : w64) (name : GoString) (fl : OsFd) (g : SegG) (r : List w8) :
    IProp GF :=
  iprop(⌜r <+: g.bs.map Prod.fst ∧ 0 ≤ fd.toInt⌝ ∗
    os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) fl ∗ fdLocksW fd fl ∗
    os.ownOff f (W64 r.length) ∗
    osMeta g.ino (DFrac.own (1 : Qp).half) g.om ∗ osBytes g.ino 0 (DFrac.own (1 : Qp).half) g.bs)

/-- The `k`th file of the tie, open on the segment `g`: its `*os.File`, fd and locks. -/
def walTieFile (dir : GoString) (write : Bool) (fls : List Loc) (k : Nat) (g : SegG) : IProp GF :=
  iprop(∃ (fd : w64) (lo lk : Option Bool), os.ownFile (fls.getD k null) fd (child dir g.name) (DFrac.own 1) ∗
    osFd fd (DFrac.own 1) (walSegFd write lo lk g.ino) ∗ fdLocks fd (walSegFd write lo lk g.ino))

/-- The `k`th file, any name and fd state (what a lock's `Close` needs). -/
def walFileAt (fls : List Loc) (k : Nat) : IProp GF :=
  iprop(∃ (fd : w64) (nm : GoString) (d : OsFd), os.ownFile (fls.getD k null) fd nm (DFrac.own 1) ∗
    osFd fd (DFrac.own 1) d ∗ fdLocks fd d)

/-- The optional legacy search range retains the iterator's directory listing
and the exact suffix whose files are already open. -/
def walReadFallback (w : Loc) (dir : GoString) (allNames selected : List GoString) : IProp GF :=
  iprop(∃ fb : Loc, structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fallback" w ↦ fb ∗
    (⌜fb = null⌝ ∨ ∃ (v : go_etcd_io.etcd.server.v3.storage.wal.walReadRange) (names : List GoString),
      fb ↦ v ∗ v.names' ↦* names ∗ ⌜0 < sint.Z v.first' ∧ sint.nat v.first' < names.length ∧
        PathFits dir ∧ names = allNames ∧ names.drop (sint.nat v.first') = selected⌝))

/-- See the file header. -/
def walReadTie (dir : GoString) (write : Bool) (s : w64 × w64) (j : Ino) (fs : List (DecFile GF))
    (lfs : List Loc) (w : Loc) : IProp GF :=
  iprop(∃ (X : List GoString) (hj : NamesH) (gs : List SegG) (fls : List Loc),
    osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
    walOutFrag (W := W) ⟨gs.map (·.ino), [(j, .except X)], if write then [dir] else []⟩ ∗
    (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗ walDirKey (W := W) dir j X ∗
    ⌜gs ≠ [] ∧ (gs.map (·.ino)).Nodup ∧ (∀ g ∈ gs, g.om.size = g.bs.length) ∧
      (∀ g, gs.head? = some g → ∀ sq ix, g.name = walFileName sq ix → ix < 2 ^ 64 → ix ≤ uint.nat s.1) ∧
      (write = true → (∀ g, gs.getLast? = some g → (walNames hj.cur).getLast? = some g.name) ∧
        ∀ t ∈ walTmps, t ∈ X) ∧
      ∃ kk, (walNames hj.cur).drop kk = gs.map (·.name)⌝ ∗
    ⌜fs.length = gs.length ∧ lfs.length = gs.length ∧ fls.length = gs.length ∧
      ∀ (k : Nat) (F : DecFile GF) (g : SegG), fs[k]? = some F → gs[k]? = some g →
        F.bs = g.bs.map (·.1) ∧ hj.cur !! g.name = some (.file g.ino) ∧
        ∃ (f : Loc) (fd : w64) (lo lk : Option Bool), fls[k]? = some f ∧
          F.S = walFileS f fd (child dir g.name) (walSegFd write lo lk g.ino) g⌝ ∗
    walReadFallback w dir (walNames hj.cur) (gs.map (·.name)) ∗
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
    walReadTie dir write s j fs lfs w ∗
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
    encEnv ∗ walCrcTable ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapBefore" w ↦ (null : Loc))

/-- **`w` is the WAL `Open` opened in `dir` at the snapshot `s`, not yet read** (the specs' handle;
sealed): the ghost handle, `openAtIndex`'s fields in write mode, `w.dirFile`
(`fileutil.OpenDir(dir)`: a shared directory fd on the WAL directory, not read), and the handle's
quarter of the call permission (the pipeline holds another, `Open` returns the half left to the client;
`ReadAll` moves this quarter into the write handle's `walDirH`: `notes/specs-only/ledger.md`,
2026-11-14, "the call permission counted twice" and "the client keeps no call permission while a WAL
is open"). The
directory fd's inode `j` is the WAL's directory key's (`walDirKey dir j X`, persistent: the read tie's
`j` by the keys' agreement, `walDirKey_agree`), which `ReadAll` needs for the handle's `walDirH`
(W3/W5 log, twenty-sixth session, obligation (f)). -/
@[no_expose] def walOpeningF (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  iprop(walOpening (W := W) w dir s ∗ walReadH true w dir s ∗ osCallPerm (callKey W.roots dir) (1 : Qp).half.half ∗
    ∃ (df : Loc) (dfd : w64) (j : Ino) (X : List GoString),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
    os.ownFile df dfd dir (DFrac.own 1) ∗ osDirFdS dfd j .idle ∗ walDirKey (W := W) dir j X)

/-- **`w` is the WAL `OpenForRead` opened in `dir` at `s`** (read mode, sealed): the lock token,
taken (`walLockedTok`: the reader holds the program's halves of the files as `Open`'s does),
`openAtIndex`'s fields in read mode, no `dirFile`. -/
@[no_expose] def walReadOnlyF (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  iprop(walLockedTok (W := W) ∗ walReadH false w dir s ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ (null : Loc))

/-- The layout facts `wal.Repair.specHeld` takes of the directory's names `hj`, the names `X` the claim leaves
out, the named segments `segs` and the last `gL` (`walCloseLeft`; `ReadAll` reads them at its look at the
invariant, `walInv_readCommitReg`, and the claim's half keeps them). -/
def CloseLeftOk (X : List GoString) (hj : NamesH) (segs : List SegG) (gL : SegG) : Prop :=
  (∀ b ∈ X, walNameP b = false) ∧ SegsNamed segs hj.cur ∧ walInos hj.cur = segs.map (·.ino) ∧
    (segs.map (·.ino)).Nodup ∧ (segs.map (·.name)).Pairwise (fun a b => go.GoStringLt a b) ∧
    (∀ g ∈ segs, ∃ sq ix : Nat, g.name = walFileName sq ix) ∧ segs.getLast? = some gL

/-- A failed handle's tail, put back (`ReadAll`'s exits before `ZeroToEnd` and after its fdatasync, which
unregister it, `walInvBody_untailL`/`walInvBody_untail`): the tails' program half empty, the program's halves
of the tail `gT` (inode `gL`'s), its file `ft` (fd and locks), and the encoder field: nil, or (the `!match`
exit) an encoder over the tail with nothing pending. -/
def walFailIdle (w : Loc) (dir : GoString) (ft : Loc) (gL : SegG) : IProp GF :=
  iprop(walTailsFrag (W := W) ∅ ∗ ∃ (gT : SegG) (fdt : w64) (d : OsFd) (e : Loc),
    segRes gT ∗ os.ownFile ft fdt (child dir gL.name) (DFrac.own 1) ∗ osFd fdt (DFrac.own 1) d ∗
    fdLocks fdt d ∗ ⌜gT.ino = gL.ino ∧ gT.om.size = gT.bs.length ∧ d.ino = gL.ino⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
    (⌜e = null⌝ ∨ ∃ c : w32, ownEncoder e (wal.fileWi ft) c []))

/-- A failed handle's tail, lent (`ReadAll`'s exits at `ZeroToEnd`'s error, `walTailPE`, and at the
fdatasync's after it, `walTailP` zeroed): registered (`walTailsFrag {dir ↦ γt}`), its write position
the record's stream, the layout's facts for `walCloseLeft`, the encoder nil. `Close`'s `w.sync()` puts it
back on success. -/
def walFailLent (Mr : WalMarshal) (w : Loc) (dir : GoString) (X : List GoString) (hj : NamesH) (ft : Loc)
    (gL : SegG) : IProp GF :=
  iprop(∃ (γt : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz k : Nat)
      (fdt : w64),
    walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) ∗
    ⌜o0 = (tailStream Mr H md cuts).length ∧ ∃ (segs : List SegG) (gLL : SegG), CloseLeftOk X hj segs gLL ∧
      gLL.ino = gL.ino⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ (null : Loc) ∗
    (walTailP (W := W) ft fdt (child dir gL.name) dir γt gL.ino H md cuts o0 sz [] k false
        (fun m bs => TailMetaZ m bs ∧ ∀ b x, o0 ≤ b → bs[b]? = some x → x.1 = 0) ∨
      walTailPE (W := W) Mr ft fdt (child dir gL.name) dir γt gL.ino H md cuts o0 k))

/-- **The fields of a failed handle** (see `walReadFailedF`). -/
def walFailH (Mr : WalMarshal) (w : Loc) (dir : GoString) : IProp GF :=
  iprop(∃ (lg : Loc) (locks : GoSlice) (ls : List Loc) (lt fp : Loc) (j : Ino) (X : List GoString) (hj : NamesH)
      (gs0 : List SegG) (gL : SegG) (fls : List Loc) (df : Loc) (dfd : w64) (ph : DirPhS),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
    locks ↦* (ls ++ [lt]) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗ walPipeH fp dir j 0 ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
      (BI.pure True : IProp GF) ∗ encEnv ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
    os.ownFile df dfd dir (DFrac.own 1) ∗ osDirFdS dfd j ph ∗ osCallPerm (callKey W.roots dir) (1 : Qp).half.half ∗
    osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
    walOutFrag (W := W) ⟨(gs0 ++ [gL]).map (·.ino), [(j, .except X)], [dir]⟩ ∗
    walNamesFrag (W := W) none ∗ walDirKey (W := W) dir j X ∗
    ⌜ls.length = gs0.length ∧ (walNames hj.cur).getLast? = some gL.name ∧
      hj.cur !! gL.name = some (.file gL.ino) ∧ (∀ t ∈ walTmps, t ∈ X) ∧
      ∀ g ∈ gs0, g.om.size = g.bs.length⌝ ∗
    ([∗list] g ∈ gs0, segRes g) ∗ ([∗list] k ↦ g ∈ gs0, walTieFile dir true fls k g) ∗
    ([∗list] k ↦ lf ∈ ls ++ [lt], fileutil.lockedFile lf (fls.getD k null)) ∗
    (walFailIdle w dir (fls.getD gs0.length null) gL ∨
      walFailLent Mr w dir X hj (fls.getD gs0.length null) gL))

/-- **`w`'s `ReadAll` in `dir` failed** (the specs' handle; sealed): only `Close` accepts it. The ghost
handle (`walReadFailed`, holding the lock token) and what `Close` reads (`walFailH`): the logger, the
directory, the locks (the segments `gs0 ++ [gL]` `openWALFiles` opened, the last the tail), the pipeline,
`unsafeNoSync`, the mutex, `dirFile`, the call permission's quarter, the directory claim's half, the out
record, the program's halves of the segments (the non-tail ones in `segRes`), and the tail, put back
(`walFailIdle`: the exits before `ZeroToEnd` and after its fdatasync unregister it) or lent
(`walFailLent`: `ZeroToEnd`'s and its fdatasync's errors). -/
@[no_expose] def walReadFailedF (Mr : WalMarshal) (w : Loc) (dir : GoString) : IProp GF :=
  iprop(walReadFailed (W := W) w dir ∗ walFailH Mr w dir)

end handle

end WalFs
end EtcdGrove
end Perennial
