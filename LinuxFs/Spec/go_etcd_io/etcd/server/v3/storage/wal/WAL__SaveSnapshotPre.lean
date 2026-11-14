/-
`w.SaveSnapshot(e)` and `w.sync()` **before `Create`'s rename** (W4 of `notes/wal-fsext-plan.md`):
`Create` (S/wal.go:180) saves the empty snapshot on a `w` that is not yet a WAL's handle (no
`dirFile`, no `fp`, `state` nil), whose encoder writes the first segment in `nm.tmp`, a file the
program owns wholly: no WAL layout tracks it, so W6's specs (over `walHandleIn`, the crash-tracked
tail) do not apply. These are their whole-resource variants, generic in the writer's states (`W`
accepted, `B` broken, as `io.writerStream`) and in what an fdatasync of the file makes of `W out`
(`S out`, a hypothesis triple: `Create` instantiates `W`/`B` with `os.fileW`/`os.fileB` and `S` with
the synced file, from `fileutil.Fdatasync.spec`). On an error the file's resources come back in a
writer state (`B`, or `W` after a failed fdatasync), for `Create`'s deferred close.

To be proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshotPre.lean`.
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeG
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DepsPkgInit

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
def snapFrame (Mr : WalMarshal) (c : w32) (sm : SnapshotMetadataM) : List w8 :=
  frame (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm), Mr.encSnap sm⟩)

/-- What an fdatasync of `f` does to the writer's state `W out`: on success `S out`, else `W out`
back (the hypothesis triple of the specs below). -/
abbrev walPreSyncOk (f : Loc) (W S : List w8 → IProp GF) : Prop :=
  ∀ out : List w8,
  {{ W out }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
  {{ (en : w64), RET #(errnoErr en); (⌜en = 0⌝ ∗ S out) ∨ (⌜en ≠ 0⌝ ∗ W out) }}

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
         (⌜err ≠ GoInterface.nil⌝ ∗ (B out pend ∨ W (out ++ pend)))) }}

/-- **`w.SaveSnapshot(e)` before the rename** (S/wal.go:1137-1162): the snapshot record of `sm`
(`ValidateSnapshotForWrite`: its conf state non-nil unless the index is 0) encoded after what the
encoder holds, then `sync` (the record within the encoder's `2^47` bound: `lim < 2^47`, `Create`'s
segment size). Success: the encoder empty, its CRC after the record, everything
accepted and synced (`S`). Error: the encoder holds anything, the writer in some broken or accepted
state (`Create` only closes the file then). `snapi`/`enti` raised to the index. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.specPre (Mr : WalMarshal) : Prop :=
  ∀ (w lg : Loc) (dir : GoString) (mds : GoSlice) (md : List w8) (e lt f : Loc) (snapi enti : w64)
    (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF) (S : List w8 → IProp GF)
    (lim : Nat) (out pend : List w8) (c : w32) (sp : Loc) (sm : SnapshotMetadataM) (cs : Bool),
  (sm.Index' = W64 0 ∨ cs = true) →
  (out ++ pend ++ snapFrame Mr c sm).length ≤ lim → lim < 2 ^ 47 → walPreSyncOk f W S →
  ⊢ io.writerStream (wal.fileWi f) lim W B -∗
    {{ encEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗
        walPreIn w lg dir mds md e lt f snapi enti ∗ ownEncoder e (wal.fileWi f) c pend ∗
        W out ∗ walSnapAt Mr sp sm cs }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
        go!"SaveSnapshot")) (Val #sp))
    {{ (err : GoInterface), RET #err;
        ∃ (snapi' enti' : w64), walPreIn w lg dir mds md e lt f snapi' enti' ∗
        ((⌜err = GoInterface.nil⌝ ∗
            ownEncoder e (wal.fileWi f) (hash.crc32.crc32c c (Mr.encSnap sm)) [] ∗
            S (out ++ pend ++ snapFrame Mr c sm)) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ ∃ (c' : w32) (pend' : List w8),
            ownEncoder e (wal.fileWi f) c' pend' ∗
            ((∃ a b : List w8, B a b) ∨ (∃ o : List w8, W o)))) }}

end spec

end EtcdGrove
end Perennial
