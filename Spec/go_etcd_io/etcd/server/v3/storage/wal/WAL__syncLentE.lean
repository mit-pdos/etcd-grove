/-
`(*wal.WAL).sync` (S/wal.go:976-1001) of a failed `ReadAll`'s handle whose tail `ZeroToEnd` left in an unknown
state (`walFailLent`'s `walTailPE` form; `WAL.Close.spec` (state `failed`)): as `WAL.sync.specLent`.

Stated by unit `closefailed`; **proved** by unit `synclent` (`WAL.sync.wp_proofLentE`, `WAL__syncLentE.lean`):
the fdatasync over the invariant step `walInvBody_syncPE` (the synced layout `syncLay_anyE`'s: F-Z, or
`syncLayP` for a torn frame past `wr`; the token kept, `Fdatasync.specWalLentE`), then the put-back by the lent
token (`walInv_untailLent`, over `walInvBody_untailL`, `p = false`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandlePend
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specLentE (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w lg : Loc) (locks : GoSlice) (ls : List Loc) (lt f : Loc)
    (fd : w64) (name dir : GoString) (γ : GName) (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o0 sz k : Nat),
  o0 = (tailStream Mr H md cuts).length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ (null : Loc) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* (ls ++ [lt]) ∗ fileutil.lockedFile lt f ∗ encEnv ∗
      walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗ walCutFrag (W := W) none ∗
      walTailPE (W := W) Mr f fd name dir γ i H md cuts o0 k }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ (null : Loc) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* (ls ++ [lt]) ∗ walCutFrag (W := W) none ∗
      ((⌜err = GoInterface.nil⌝ ∗ walTailsFrag (W := W) ∅ ∗ os.ownFile f fd name (DFrac.own 1) ∗
          (∃ d : OsFd, osFd fd (DFrac.own 1) d ∗ fdLocks fd d ∗ ⌜d.ino = i⌝) ∗
          ∃ g : SegG, segRes g ∗ ⌜g.ino = i ∧ g.om.size = g.bs.length⌝) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗
          walTailPE (W := W) Mr f fd name dir γ i H md cuts o0 k)) }}

end spec

end EtcdGrove
end Perennial
