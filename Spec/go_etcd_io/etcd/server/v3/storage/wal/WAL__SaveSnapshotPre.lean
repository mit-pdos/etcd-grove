/-
`w.SaveSnapshot(e)` and `w.sync()` **before `Create`'s rename** (W4 of `notes/wal-fsext-plan.md`):
`Create` (S/wal.go:180) saves the empty snapshot on a `w` that is not yet a WAL's handle (no
`dirFile`, no `fp`, `state` nil), whose encoder writes the first segment in `nm.tmp`, a file the
program owns wholly: no WAL layout tracks it, so W6's specs (over `walHandleIn`, the crash-tracked
tail) do not apply. `sync`'s whole-resource variant is here, and what `SaveSnapshot.spec`'s state `pre`
(`WAL__SaveSnapshot.lean`) is written in; both are generic in the writer's states (`W`
accepted, `B` broken, as `io.writerStream`) and in what an fdatasync of the file makes of `W out`
(`S out`, a hypothesis triple: `Create` instantiates `W`/`B` with `os.fileW`/`os.fileB` and `S` with
the synced file, from `fileutil.Fdatasync.spec`). On an error the file's resources come back in a
writer state (`B`, or `W` after a failed fdatasync), for `Create`'s deferred close.

`sync.specPre` is proved in `Proof/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshotPre.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeG
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DepsPkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`Create`'s `w` before the rename** (S/wal.go:164-175): its logger, directory and metadata, no
fsync skipping, its mutex, `snapi`/`enti`, the encoder `e` (non-nil: `sync` flushes it only then),
and one locked file `lt` (of the `*os.File` `f`) in `locks`. -/
def walPreIn (w lg : Loc) (dir : GoString) (mds : GoSlice) (md : List w8) (e lt f : Loc)
    (snapi enti : w64) : IProp GF :=
  iprop(∃ locks : GoSlice,
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"metadata" w ↦ mds ∗ mds ↦*□ md ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
      (BI.pure True : IProp GF) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ enti ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ snapi ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗ ⌜e ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
    locks ↦* [lt] ∗ ownSliceCap Loc locks (DFrac.own 1) ∗ fileutil.lockedFile lt f)

/-- The frame of the snapshot record of `sm`, the chain's CRC before it `c`. -/
def snapFrame (Mr : WalMarshal) (c : w32) (sm : SnapshotMetadataM) (al : Bool) : List w8 :=
  frame (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al), Mr.encSnap sm al⟩)

/-- What an fdatasync of `f` does to the writer's state `W out`: on success `S out`, else `W out`
back, the failure witnessing that the file system can fail on an inode (`¬ Fs.FsNoErrIno`, wal-fsfix2;
the hypothesis triple of the specs below). -/
abbrev walPreSyncOk (f : Loc) (W S : List w8 → IProp GF) : Prop :=
  ∀ out : List w8,
  {{ W out }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
  {{ (en : w64), RET #(errnoErr en); (⌜en = 0⌝ ∗ S out) ∨ (⌜en ≠ 0 ∧ ¬ Fs.FsNoErrIno⌝ ∗ W out) }}

/-- What `w.tail().Seek(0, io.SeekCurrent)` gives from the writer's state `W out` (the tail is the file `f`):
the accepted length, the state kept (`SaveSnapshot`'s offset test before the rename, the fork's fix 0007; a
hypothesis triple as `walPreSyncOk`, which `Create` proves of its file's stream, whose bound is `lim`). -/
abbrev walPreSeekOk (f : Loc) (W : List w8 → IProp GF) (lim : Nat) : Prop :=
  ∀ out : List w8, out.length ≤ lim →
  {{ W out }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Seek")) (Val #(W64 0))) (Val #(W64 1)))
  {{ RET (PairV #(W64 (out.length : Int)) #GoInterface.nil); W out }}

/-- **`w.sync()` before the rename** (S/wal.go:967-992): flushes the encoder and fdatasyncs the file
(`unsafeNoSync` false). Success: everything accepted, synced (`S`). Error: the flush's broken state, or
the fdatasync's. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre : Prop :=
  ∀ (w lg : Loc) (dir : GoString) (mds : GoSlice) (md : List w8) (e lt f : Loc) (snapi enti : w64)
    (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF) (S : List w8 → IProp GF)
    (lim : Nat) (out pend : List w8) (c : w32),
  out.length + pend.length ≤ lim → walPreSyncOk f W S →
  ⊢ io.writerStream (wal.fileWi f) lim W B -∗
    {{ encEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗
        walPreIn w lg dir mds md e lt f snapi enti ∗ ownEncoder e (wal.fileWi f) c pend ∗ W out }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
        go!"sync")) (Val #()))
    {{ (err : GoInterface), RET #err;
        walPreIn w lg dir mds md e lt f snapi enti ∗ ownEncoder e (wal.fileWi f) c [] ∗
        ((⌜err = GoInterface.nil⌝ ∗ S (out ++ pend)) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ (B out pend ∨ (⌜¬ Fs.FsNoErrIno⌝ ∗ W (out ++ pend))))) }}

end spec

end EtcdGrove
end Perennial
