/- Lean-first (no Rocq counterpart).

# `fileutil.Fdatasync` of an idle tail (the W7-W12 log of `notes/wal-fsext-plan.md`, eighth session)

`syscall.Fdatasync` and `fileutil.Fdatasync` (`int(f.Fd())`, then the system call) re-proved over
`wp_idleFsync` (`TailFsyncIdle.lean`), in place of `wp_osFsync`, as `TailFdatasync.lean` does over
`wp_tailFsync` for a registered tail: the file at the last `.wal` name of the WAL directory's claim,
the program holding half of its `OsMeta` and bytes and half of the claim. On success the halves are the
synced ones; on failure nothing changes.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailFsyncIdle
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc

section idle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [syscall_sem : syscall.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`syscall.Fdatasync` of an idle tail** (see the file header). -/
theorem syscall.Fdatasync.wp_idle (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (b : GoString) (m : OsMeta)
    (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd)
    (hb : (walNames hj.cur).getLast? = some b) (hi : hj.cur !! b = some (.file d.ino))
    (hlen : bs.length = m.size) :
    {{ walAreaOk walCodec Mr R jr r ∗ osFd fd dq d ∗ walDirKey (W := W) dir j X ∗
        osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗ walTailsFrag (W := W) ∅ ∗
        walCutFrag (W := W) none ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! syscall.Fdatasync)) (Val #fd))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗ walDirKey (W := W) dir j X ∗
        osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗ walTailsFrag (W := W) ∅ ∗
        walCutFrag (W := W) none ∗
        ((⌜e = 0⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1))) ∨
         (⌜e ≠ 0⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) }} := by
  wp_start as ⟨#Harea, Hfd, Hk, Hn, Hf, Hcf, Hm, Hb⟩
  wp_apply wp_idleFsync Mr R jr r dir j X hj b m bs fd dq d _ hb hi hlen
    $$ Harea Hfd Hk Hn Hf Hcf Hm Hb as %e Hfd Hk Hn Hf Hcf Hr
  iapply wp_errno
  iapply HΦ
  iframe Hfd Hk Hn Hf Hcf
  icases Hr with (⟨%he, Hr⟩ | ⟨%he, Hr⟩)
  · ileft; iframe Hr; ipureintro; exact he
  · iright; iframe Hr; ipureintro; exact he.1

/-- **`fileutil.Fdatasync` of an idle tail** (see the file header). -/
theorem fileutil.Fdatasync.wp_idle (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64)
    (name dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (b : GoString) (m : OsMeta)
    (bs : List ByteG) (dqf dq : DFrac) (d : OsFd)
    (hb : (walNames hj.cur).getLast? = some b) (hi : hj.cur !! b = some (.file d.ino))
    (hlen : bs.length = m.size) :
    {{ walAreaOk walCodec Mr R jr r ∗ os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        walDirKey (W := W) dir j X ∗
        osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗ walTailsFrag (W := W) ∅ ∗
        walCutFrag (W := W) none ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
    {{ (e : w64), RET #(errnoErr e); os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        walDirKey (W := W) dir j X ∗
        osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗ walTailsFrag (W := W) ∅ ∗
        walCutFrag (W := W) none ∗
        ((⌜e = 0⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1))) ∨
         (⌜e ≠ 0⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) }} := by
  wp_start as ⟨#Harea, Hf, Hfd, Hk, Hn, Htf, Hcf, Hm, Hb⟩
  wp_auto
  wp_apply wp_Fd f fd name dqf $$ Hf as Hf
  wp_apply syscall.Fdatasync.wp_idle Mr R jr r dir j X hj b m bs fd dq d hb hi hlen
    $$ [Harea Hfd Hk Hn Htf Hcf Hm Hb] as %e ⟨Hfd, Hk, Hn, Htf, Hcf, Hr⟩
  · iframe; iexact Harea
  iapply HΦ
  iframe

end idle

end WalFs
end EtcdGrove
end Perennial

end
