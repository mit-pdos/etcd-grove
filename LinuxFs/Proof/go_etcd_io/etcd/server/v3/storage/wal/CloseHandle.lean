/-
`Close`'s vocabulary (W10 of `notes/wal-fsext-plan.md`; the W7-W12 log, fourth session):

* `walHandleC`: the open WAL's handle after `Close` closed its file pipeline (`w.fp` nil, the pipeline's
  resources gone): `walHandleIn` (`Handle.lean`) but for `w.fp ↦ fp ∗ walPipeH fp dir j h.pc`. `Close`'s
  `w.sync()` runs on it (`WAL.sync.specC`, `LinuxFs/Spec/.../wal/WAL__syncC.lean`: `sync.spec` with
  this handle; `sync` never reads `w.fp`).
* `WalCloseLaw`: the WAL invariant's law `Close` needs at a program step once every file is closed
  (a hypothesis, for the invariant's owner, W1): the client's update committed unchanged after the
  sync, then the handle's halves parked again (the tail, idle and synced, unregistered from the tails'
  authority; the directory's claim; the pipeline names) and the lock token given back.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section synced
variable [GooseExts]

/-- **The tail synced** (`TailMeta`, every byte durable; the W7-W12 log, sixth session): what
`WAL.sync.specC`'s post gives of the tail (its fdatasync: `OsMeta.synced`, the bytes `durB`), so that
`Close`'s unregistration establishes the WAL's `TailSynced` (`Inv.lean`). -/
def TailMetaS (m : Fs.OsMeta) (bs : List Fs.ByteG) : Prop :=
  TailMeta m bs ∧ ∀ y ∈ bs, y = Fs.durB y.1

theorem TailMetaS.meta {m : Fs.OsMeta} {bs : List Fs.ByteG} (h : TailMetaS m bs) : TailMeta m bs := h.1

/-- The tail after a successful fdatasync (`wp_osFsync`'s post): synced. -/
theorem TailMetaS.of_sync {m : Fs.OsMeta} {bs : List Fs.ByteG} (h : TailMeta m bs) :
    TailMetaS m.synced (bs.map (fun x => Fs.durB x.1)) := by
  refine ⟨⟨by simp [OsMeta.synced, h.1], h.2.1, h.2.2.1.synced, rfl, rfl, PastZ.synced m⟩, fun y hy => ?_⟩
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl

end synced

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header: `walHandleIn` with `w.fp` nil and no pipeline; the WAL directory's inode
`j` a parameter (the pipeline's leftover name is claimed on it); the naming fact `nmd` as `walHandleIn`'s
(`emp` for `Create`'s cleanup, `WAL.Close.specU`). -/
def walHandleC (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (j : Ino) (h : WalHS)
    (tm : Fs.OsMeta → List Fs.ByteG → Prop := TailMeta) (nmd : IProp GF := walNamed (W := W) dir) :
    IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ (lg df sp e lt f : Loc) (mds locks : GoSlice) (lfs : List Loc) (fd dfd : w64)
      (name dnm : GoString) (rc : GoFunc),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
    os.ownFile df dfd dnm (DFrac.own 1) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"metadata" w ↦ mds ∗
    recBytes mds (some h.md) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp ∗
    P.hsIn sp h.st ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"decoder" w ↦ GoInterface.nil ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"readClose" w ↦ rc ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
      (BI.pure True : IProp GF) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ h.enti ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ h.snapi ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗ ⌜e ≠ null⌝ ∗
    ownEncoder e (wal.fileWi f) (h.crc Mr) h.pend ∗
    walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out tm ∗
    walDirH (W := W) dir j dfd h.ino name h.pc nmd ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
    locks ↦* lfs ∗ ownSliceCap Loc locks (DFrac.own 1) ∗ ⌜lfs.getLast? = some lt⌝ ∗
    ([∗list] lf ∈ lfs.dropLast, walLockH lf) ∗
    fileutil.lockedFile lt f ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ (null : Loc) ∗
    encEnv ∗ walCrcTable ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
    walOpenW (W := W) w dir ∗
    ⌜WalHS.Split Mr h ∧ 0 ≤ fd.toInt ∧ h.o0 + h.out.length ≤ h.sz ∧ h.sz ≤ 0xffffffff000 ∧
      ((h.rest = 0 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi)) ∧
        walMaxSnapIdx (h.H.map WalOpG.toM) ≤ uint.nat h.snapi) ∧
      max (uint.nat h.enti) (uint.nat h.snapi) + 1 < 2 ^ 64⌝)

end handle

section law
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **`Close`'s put-back** (see the file header), at a program step (`notCrashed`): the WAL in `dir`
with its tail `ino` (record `γ`, every record written, `wr` the tail stream's end, no write in flight;
the program's halves of its `OsMeta` and bytes, synced: `TailMetaS`), the directory's claim's half and
key, the pipeline names' claims (`b`, `b'`: the pipeline's leftover name and the one the handle kept,
both of `walTmps`), the record of what is out, the lock holder's halves (the tails' authority with
this tail, no registration pending), the ghost handle with the lock token (`walOpenW`), the purge right
and the history synced; the client's update. Gives the update's `Q d` (committed unchanged), the
history synced in `d`'s terms, and the free lock token. The unregistration must establish the WAL's
`TailIdle` (`walTailsRes`'s `WalTailIdle`, `Inv.lean`): the record's `wr` is the tail stream's end (all
written) and `TailMetaS m bs` (synced: `lo = size = hi`, every byte durable) gives the layout's
`TailExact` and `TailSynced` by agreement of the halves. -/
def WalCloseLaw (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : Prop :=
  ∀ (w : Loc) (dir : GoString) (γ γt : GName) (ino j : Ino) (X : List GoString) (hj : NamesH)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat) (m : OsMeta)
    (bs : List ByteG) (b b' : GoString) (Q : WalDur → IProp GF),
  TailMetaS m bs → wr = (tailStream Mr H md cuts).length → b ∈ walTmps → b' ∈ walTmps →
  ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
    walTailKey (W := W) dir γ -∗ tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
    osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs -∗
    walDirKey (W := W) dir j X -∗ osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj -∗
    tmpClaim (hG := ⟨G, L⟩) j b -∗ tmpClaim (hG := ⟨G, L⟩) j b' -∗
    walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ -∗
    walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) -∗ walNamesFrag (W := W) none -∗
    walOpenW (W := W) w dir -∗ walPurgeW (W := W) w dir -∗ walSyncedLb (W := W) dir H.length -∗
    (AU <{ ∃∃ d : WalDur, walDiskAt (W := W) dir d }> @ walAuMask, ∅
      <{ walDiskAt (W := W) dir d, COMM Q d }>) ={⊤}=∗
    notCrashed (hC := L.goose_crashGS) ∗
      ∃ d, Q d ∗ walSyncedLb (W := W) dir d.H.length ∗ walUnlockedTok (W := W)

end law

end WalFs
end EtcdGrove
end Perennial
