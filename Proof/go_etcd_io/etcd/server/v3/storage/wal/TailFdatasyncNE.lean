/- Lean-first (no Rocq counterpart).

# The tail's fdatasync with no error (`NoIoErr`, `notes/wal-units/noioerr.md`)

Over a semantics whose steps satisfy the premise **no I/O error on chosen files**
(`FsStepSat (NoIoErr S)`, every inode covered: `hS`), the tail's fdatasync succeeds: `wp_tailFsyncNE`
(`wp_tailFsync` strengthened by `wp_ext_post`: its step returns 0), and the wrappers
`syscall.Fdatasync.wp_tailNE`, `fileutil.Fdatasync.wp_tailNE`/`wp_tailWNE` (the proofs of
`TailFdatasync.lean` with the failure arm gone).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailFdatasync
public import GooseLang.Ext.Fs.NoIoErrSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section tail
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **The tail's fdatasync with no error** (see the file header). -/
theorem wp_tailFsyncNE (hS : ∀ st i, Sio.ino st i) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (dir : GoString) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (m : OsMeta) (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd)
    (Φ : val → IProp GF) (ic : Nat) (hm : TailMetaW m bs) (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ walIncLb (W := W) dir ic -∗ osFd fd dq d -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
      osMeta d.ino (DFrac.own (1 : Qp).half) m -∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (osFd fd dq d -∗ walTailKey (W := W) dir γ -∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m.synced -∗
        osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) -∗
        walSyncedLb (W := W) dir ic H.length -∗ Φ (#(0 : w64))) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  iintro #Harea #Hil Hfd Hk Hv Hcf Hm Hb HΦ
  iapply wp_ext_post "Fsync" (#fd) (by simp) (· = #(0 : w64)) (fsync_noErr hS fd) Φ
  iapply wp_tailFsync Mr R jr r dir γ H md cuts wr m bs fd dq d _ ic hm hwr
    $$ Harea Hil Hfd Hk Hv Hcf Hm Hb
  iintro %e Hfd Hk Hv Hcf Hr %he
  have he0 : e = 0 := go.intoVal_inj he
  subst he0
  icases Hr with (⟨-, Hm, Hb, Hs⟩ | ⟨%h0, -, -⟩)
  · iapply HΦ $$ Hfd Hk Hv Hcf Hm Hb Hs
  · exact absurd rfl h0.1

/-- **`syscall.Fdatasync` of the tail with no error** (`syscall.Fdatasync.wp_tail`). -/
theorem syscall.Fdatasync.wp_tailNE [syscall.Assumptions] (hS : ∀ st i, Sio.ino st i)
    (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (m : OsMeta) (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd)
    (hm : TailMetaW m bs) (hwr : wr = (tailStream Mr H md cuts).length) (ic : Nat) :
    {{ walAreaOk walCodec Mr R jr r ∗ walIncLb (W := W) dir ic ∗ osFd fd dq d ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! syscall.Fdatasync)) (Val #fd))
    {{ RET #(errnoErr 0); osFd fd dq d ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
        osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) ∗
        walSyncedLb (W := W) dir ic H.length }} := by
  wp_start as ⟨#Harea, #Hil, Hfd, Hk, Hv, Hcf, Hm, Hb⟩
  wp_apply wp_tailFsyncNE hS Mr R jr r dir γ H md cuts wr m bs fd dq d _ ic hm hwr
    $$ Harea Hil Hfd Hk Hv Hcf Hm Hb as Hfd Hk Hv Hcf Hm Hb Hs
  iapply wp_errno
  iapply HΦ
  iframe

/-- **`fileutil.Fdatasync` of the tail with no error** (`fileutil.Fdatasync.wp_tail`). -/
theorem fileutil.Fdatasync.wp_tailNE [syscall.Assumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] (hS : ∀ st i, Sio.ino st i)
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64)
    (name dir : GoString) (γ : GName) (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (hwr : o0 + out.length = (tailStream Mr H md cuts).length) (ic : Nat) :
    {{ walAreaOk walCodec Mr R jr r ∗ walIncLb (W := W) dir ic ∗ walTailW (W := W) f fd name dir γ i H md cuts o0 sz out ∗
        walCutFrag (W := W) none }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
    {{ RET #(errnoErr 0); walTailW (W := W) f fd name dir γ i H md cuts o0 sz out ∗
        walCutFrag (W := W) none ∗ walSyncedLb (W := W) dir ic H.length }} := by
  wp_start as ⟨#Harea, #Hil, Hw, Hcf⟩
  unfold walTailW
  icases Hw with ⟨Hf, ⟨%rd, %lo, %lk, Hfd, Hlkt⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  wp_auto
  wp_apply wp_Fd f fd name (DFrac.own 1) $$ Hf as Hf
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0 + out.length, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  wp_apply syscall.Fdatasync.wp_tailNE hS Mr R jr r dir γ H md cuts (o0 + out.length) m bs fd
    (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ hp.2.1.win hwr ic $$ [Harea Hfd Hk Hv Hcf Hm Hb]
    as ⟨Hfd, Hk, Hv, Hcf, Hm, Hb, #Hs⟩
  · iframe Hil; iframe; iexact Harea
  iapply HΦ
  iframe Hcf Hs
  iframe Hf Hoff Hk
  isplitl [Hfd Hlkt]
  · iexists rd, lo, lk; iframe
  iexists m.synced, (bs.map (fun x => durB x.1))
  iframe Hm Hb
  isplitr
  · ipureintro
    exact ⟨by simp [OsMeta.synced, hp.1], hp.2.1.synced, hp.2.2.1, hp.2.2.2.1, LoWr.of_exact rfl rfl⟩
  · iapply tailVar_unfold $$ Hv

/-- **`fileutil.Fdatasync` of the tail in a resize window with no error**
(`fileutil.Fdatasync.wp_tailW`): the tail exact again, every byte durable. -/
theorem fileutil.Fdatasync.wp_tailWNE [syscall.Assumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] (hS : ∀ st i, Sio.ino st i)
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64)
    (name dir : GoString) (γ : GName) (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (hwr : o0 + out.length = (tailStream Mr H md cuts).length) (ic : Nat) :
    {{ walAreaOk walCodec Mr R jr r ∗ walIncLb (W := W) dir ic ∗
        walTailW (W := W) f fd name dir γ i H md cuts o0 sz out (tm := TailMetaW) ∗
        walCutFrag (W := W) none }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
    {{ RET #(errnoErr 0); walCutFrag (W := W) none ∗
        walTailW (W := W) f fd name dir γ i H md cuts o0 sz out (tm := TailMetaS) ∗
        walSyncedLb (W := W) dir ic H.length }} := by
  wp_start as ⟨#Harea, #Hil, Hw, Hcf⟩
  unfold walTailW
  icases Hw with ⟨Hf, ⟨%rd, %lo, %lk, Hfd, Hlkt⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  wp_auto
  wp_apply wp_Fd f fd name (DFrac.own 1) $$ Hf as Hf
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0 + out.length, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  wp_apply syscall.Fdatasync.wp_tailNE hS Mr R jr r dir γ H md cuts (o0 + out.length) m bs fd
    (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ hp.2.1 hwr ic $$ [Harea Hfd Hk Hv Hcf Hm Hb]
    as ⟨Hfd, Hk, Hv, Hcf, Hm, Hb, #Hs⟩
  · iframe Hil; iframe; iexact Harea
  iapply HΦ
  iframe Hcf Hs
  iframe Hf Hoff Hk
  isplitl [Hfd Hlkt]
  · iexists rd, lo, lk; iframe
  iexists m.synced, (bs.map (fun x => durB x.1))
  iframe Hm Hb
  isplitr
  · ipureintro
    exact ⟨by simp [OsMeta.synced, hp.1], hp.2.1.syncedS, hp.2.2.1, hp.2.2.2.1, LoWr.of_exact rfl rfl⟩
  · iapply tailVar_unfold $$ Hv

end tail

end WalFs
end EtcdGrove
end Perennial

end
