/-
`(*wal.WAL).sync` (S/wal.go:967-992) of a handle without an encoder (`Open`'s, before `ReadAll`:
`Close` of it, `WAL.Close.specOpening`): no flush, `fileutil.Fdatasync` of the last lock's file, which
is the WAL's tail, never registered (idle): the file at the last `.wal` name of the WAL directory's
claim, of which the program holds half (`wp_idleFsync`, `TailFsyncIdle.lean`). On success the
program's halves of the tail are the synced ones (`OsMeta.synced`, every byte `durB`); on failure
nothing changes. The fields read are framed through. Lean-first (W10 of `notes/wal-fsext-plan.md`,
the W7-W12 log's eighth session).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIdle (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w lg : Loc) (locks : GoSlice) (ls : List Loc) (lt f : Loc)
    (fd : w64) (name dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (b : GoString)
    (fl : OsFd) (m : OsMeta) (bs : List ByteG),
  (walNames hj.cur).getLast? = some b → hj.cur !! b = some (.file fl.ino) → bs.length = m.size →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ (null : Loc) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* (ls ++ [lt]) ∗ fileutil.lockedFile lt f ∗ encEnv ∗
      os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) fl ∗
      walDirKey (W := W) dir j X ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
      walTailsFrag (W := W) ∅ ∗ walCutFrag (W := W) none ∗
      osMeta fl.ino (DFrac.own (1 : Qp).half) m ∗ osBytes fl.ino 0 (DFrac.own (1 : Qp).half) bs }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ (null : Loc) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* (ls ++ [lt]) ∗
      os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) fl ∗
      walDirKey (W := W) dir j X ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
      walTailsFrag (W := W) ∅ ∗ walCutFrag (W := W) none ∗
      ((⌜err = GoInterface.nil⌝ ∗ osMeta fl.ino (DFrac.own (1 : Qp).half) m.synced ∗
          osBytes fl.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1))) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ osMeta fl.ino (DFrac.own (1 : Qp).half) m ∗
          osBytes fl.ino 0 (DFrac.own (1 : Qp).half) bs)) }}

end spec

end EtcdGrove
end Perennial
