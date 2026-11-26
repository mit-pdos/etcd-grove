/-
`(*wal.WAL).sync` (S/wal.go:976-1001) of a failed `ReadAll`'s handle whose tail is put back (`walFailIdle`,
`ReadDefs.lean`; `WAL.Close.spec` (state `failed`)): `WAL.sync.specIdle` with the encoder field nil or an encoder over the
tail's file with nothing pending (`ReadAll`'s `!match` exit made it), whose `flush` writes nothing. Unit
`closefailed`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit

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
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIdleF (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w lg : Loc) (locks : GoSlice) (ls : List Loc) (lt f : Loc)
    (fd : w64) (name dir : GoString) (i : Nat) (I : GMap GoString Nat) (j : Ino) (X : List GoString) (hj : NamesH) (b : GoString)
    (fl : OsFd) (m : OsMeta) (bs : List ByteG) (e : Loc),
  (walNames hj.cur).getLast? = some b → hj.cur !! b = some (.file fl.ino) → bs.length = m.size →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
      (⌜e = null⌝ ∨ ∃ c : w32, ownEncoder e (wal.fileWi f) c []) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* (ls ++ [lt]) ∗ fileutil.lockedFile lt f ∗ encEnv ∗
      os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) fl ∗
      walDirKey (W := W) dir i j X ∗ walIncQ (W := W) I ∗ ⌜incOf I dir = i⌝ ∗
      osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
      walTailsFrag (W := W) ∅ ∗ walCutFrag (W := W) none ∗
      osMeta fl.ino (DFrac.own (1 : Qp).half) m ∗ osBytes fl.ino 0 (DFrac.own (1 : Qp).half) bs }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
      (⌜e = null⌝ ∨ ∃ c : w32, ownEncoder e (wal.fileWi f) c []) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* (ls ++ [lt]) ∗
      os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) fl ∗
      walDirKey (W := W) dir i j X ∗ walIncQ (W := W) I ∗ ⌜incOf I dir = i⌝ ∗
      osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
      walTailsFrag (W := W) ∅ ∗ walCutFrag (W := W) none ∗
      ((⌜err = GoInterface.nil⌝ ∗ osMeta fl.ino (DFrac.own (1 : Qp).half) m.synced ∗
          osBytes fl.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1))) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ osMeta fl.ino (DFrac.own (1 : Qp).half) m ∗
          osBytes fl.ino 0 (DFrac.own (1 : Qp).half) bs)) }}

end spec

end EtcdGrove
end Perennial
