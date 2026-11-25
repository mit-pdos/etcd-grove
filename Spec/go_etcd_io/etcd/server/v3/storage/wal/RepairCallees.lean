/-
The WAL-tail callees of `wal.Repair` over `fsExt` (W7 of `notes/wal-fsext-plan.md`; the W7-W12 log,
thirteenth session). `Repair` registers the last segment's tail pending (`walInvRegisterPendLaw`: the
pending token, kind `true`), so its truncate and fsync step the tail by that token, the file's offset
framed (after `io.Copy` it is the file's end).

* `os.File.Truncate.specRepTail`: `f.Truncate(tg)` of the registered, not yet zeroed tail at the end of
  the frames `Repair` read, `tg ∈ [wr, size]` (`wr` the record's stream end; past it a pending run, P6, a
  nonzero byte of which `TailMetaRP` names): `os.File.Truncate.specAu` with `walTail_truncSupR` at the
  pending token (F-Z or `RepOld`, the lent registry's, at every attempt; L4). On success the tail's size
  is `tg`, its window open (`TailMetaRW`); on an error the file handle back (`Repair`'s deferred
  `f.Close()`), the tail lost (the window may stay open: `Repair.spec`'s `false` arm, ledger 2026-11-14).
  Proved (`os.File.Truncate.wp_specRepTail`, `RepairTruncate.lean`).
* `fileutil.Fsync.specRepTail`: `fileutil.Fsync(f.File)` after the truncate to `tg` landed: the window
  closed and the token kept (`syncLay_anyE`: F-Z, or `TailPend` with the run past `wr` as the synced
  layout's `old`, `syncLayP`; P6: no F-Z past a pending run, so the token does not turn into the key, and
  `Repair` unregisters the tail by the token, `walInvBody_untailL`), the tail exact and synced
  (`TailMetaR`, the zeros known from the size on, every byte durable); on an error the file handle back,
  the tail lost. Proved (`fileutil.Fsync.wp_specRepTail`, `RepairFsync.lean`, over `walInvBody_syncPE`).
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairTailDefs

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
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **`f.Truncate(wr)` of `Repair`'s registered tail** (see the file header). -/
abbrev os.File.Truncate.specRepTail (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 tg sz k : Nat) (off : w64),
  o0 ≤ tg → tg ≤ sz → o0 = (tailStream Mr H md cuts).length →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗
      walTailPO (W := W) f fd name dir γ i H md cuts o0 sz k true off
        (TailMetaRP Mr (tailCrc Mr H md cuts) o0 tg) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #(W64 tg)))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗
        walTailPO f fd name dir γ i H md cuts o0 tg k true off (TailMetaRWP Mr (tailCrc Mr H md cuts) o0)) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ os.ownFile f fd name (DFrac.own 1) ∗
        (∃ (rd : Bool) (lo lk : Option Bool), osFd fd (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ ∗
          fdLocks fd ⟨i, rd, true, lo, lk⟩) ∗ os.ownOff f off) }}

/-- **`fileutil.Fsync(f.File)` of `Repair`'s truncated tail** (see the file header). -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specRepTail (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 tg k : Nat) (off : w64),
  o0 = (tailStream Mr H md cuts).length →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗
      walTailPO (W := W) f fd name dir γ i H md cuts o0 tg k true off
        (TailMetaRWP Mr (tailCrc Mr H md cuts) o0) ∗
      walCutFrag (W := W) none }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync)) (Val #f))
  {{ (err : GoInterface), RET #err; walCutFrag (W := W) none ∗ os.ownFile f fd name (DFrac.own 1) ∗
      (∃ (rd : Bool) (lo lk : Option Bool), osFd fd (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ ∗
          fdLocks fd ⟨i, rd, true, lo, lk⟩) ∗ os.ownOff f off ∗
      ((⌜err = GoInterface.nil⌝ ∗ (∃ k' : Nat, walLentTokB (W := W) dir γ k' true) ∗
          ∃ (m : OsMeta) (bs : List ByteG),
            osMeta i (DFrac.own (1 : Qp).half) m ∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗
            ⌜m.size = tg ∧ TailMetaR m bs ∧ (∀ z, m.zf = some z → m.size ≤ z) ∧ ∀ y ∈ bs, y = Fs.durB y.1⌝ ∗
            (letI := walAllG (W := W); ghostVar γ (1 : Qp).half ((H, md, cuts, o0, i, none) : TailG))) ∨
       ⌜err ≠ GoInterface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
