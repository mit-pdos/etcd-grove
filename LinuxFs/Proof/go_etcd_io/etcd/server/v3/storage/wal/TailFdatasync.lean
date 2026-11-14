/- Lean-first (no Rocq counterpart).

# `fileutil.Fdatasync` of the WAL's tail (W6 of `notes/wal-fsext-plan.md`, "W6 implementation log")

`syscall.Fdatasync` and `fileutil.Fdatasync` (`int(f.Fd())`, then the system call) re-proved over the
crash-aware step `wp_tailFsync` (`TailFsync.lean`), in place of `wp_osFsync`: the tail's writer state
`walTailW` with every record of the history flushed (`o0 + |out|` the end of the tail's stream). On
success the tail is synced (`walTailW` again, its `OsMeta` and bytes synced, hidden) and the history is
synced (`walSyncedLb dir |H|`); on failure nothing changes. The lock token's pending-cut flag
(`walCutFrag none`) goes through.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailFsync
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc

section tail
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [syscall_sem : syscall.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- `TailMeta` of the synced tail. -/
theorem TailMeta.synced {m : OsMeta} {bs : List ByteG} (h : TailMeta m bs) :
    TailMeta m.synced (bs.map (fun x => durB x.1)) :=
  ⟨by simp [OsMeta.synced, h.1], h.2.1, h.2.2.1.synced, rfl, rfl, PastZ.synced m⟩

/-- **`syscall.Fdatasync` of the tail** (see the file header). -/
theorem syscall.Fdatasync.wp_tail (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (m : OsMeta) (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd)
    (hm : TailMetaW m bs) (hwr : wr = (tailStream Mr H md cuts).length) :
    {{ walAreaOk walCodec Mr R jr r ∗ osFd fd dq d ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! syscall.Fdatasync)) (Val #fd))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        ((⌜e = 0⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) ∗
            walSyncedLb (W := W) dir H.length) ∨
         (⌜e ≠ 0⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) }} := by
  wp_start as ⟨#Harea, Hfd, Hk, Hv, Hcf, Hm, Hb⟩
  wp_apply wp_tailFsync Mr R jr r dir γ H md cuts wr m bs fd dq d _ hm hwr
    $$ Harea Hfd Hk Hv Hcf Hm Hb as %e Hfd Hk Hv Hcf Hr
  iapply wp_errno
  iapply HΦ
  iframe Hfd Hk Hv Hcf
  icases Hr with (⟨%he, Hr⟩ | ⟨%he, Hr⟩)
  · ileft; iframe Hr; ipureintro; exact he
  · iright; iframe Hr; ipureintro; exact he.1

theorem tailVar_unfold (γ : GName) (tg : TailG) :
    tailVar (W := W) γ tg ⊢ (letI := walAllG (W := W); ghostVar γ (1 : Qp).half tg) := by
  unfold tailVar; exact .rfl

/-- **`fileutil.Fdatasync` of the tail** (see the file header): over the writer state `walTailW`,
every record flushed. -/
theorem fileutil.Fdatasync.wp_tail (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64)
    (name dir : GoString) (γ : GName) (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (hwr : o0 + out.length = (tailStream Mr H md cuts).length) :
    {{ walAreaOk walCodec Mr R jr r ∗ walTailW (W := W) f fd name dir γ i H md cuts o0 sz out ∗
        walCutFrag (W := W) none }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
    {{ (e : w64), RET #(errnoErr e); walTailW (W := W) f fd name dir γ i H md cuts o0 sz out ∗
        walCutFrag (W := W) none ∗ ((⌜e = 0⌝ ∗ walSyncedLb (W := W) dir H.length) ∨ ⌜e ≠ 0⌝) }} := by
  wp_start as ⟨#Harea, Hw, Hcf⟩
  unfold walTailW
  icases Hw with ⟨Hf, ⟨%rd, Hfd⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  wp_auto
  wp_apply wp_Fd f fd name (DFrac.own 1) $$ Hf as Hf
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0 + out.length, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  wp_apply syscall.Fdatasync.wp_tail Mr R jr r dir γ H md cuts (o0 + out.length) m bs fd
    (DFrac.own 1) ⟨i, rd, true⟩ hp.2.1.win hwr $$ [Harea Hfd Hk Hv Hcf Hm Hb]
    as %e ⟨Hfd, Hk, Hv, Hcf, Hr⟩
  · iframe; iexact Harea
  iapply HΦ
  iframe Hcf
  icases Hr with (⟨%he, Hm, Hb, #Hs⟩ | ⟨%he, Hm, Hb⟩)
  · isplitl [Hf Hfd Hoff Hk Hm Hb Hv]
    · iframe Hf Hoff Hk
      isplitl [Hfd]
      · iexists rd; iexact Hfd
      iexists m.synced, (bs.map (fun x => durB x.1))
      iframe Hm Hb
      isplitr
      · ipureintro
        exact ⟨by simp [OsMeta.synced, hp.1], hp.2.1.synced, hp.2.2.1, hp.2.2.2.1, LoWr.of_exact rfl rfl⟩
      · iapply tailVar_unfold $$ Hv
    · ileft; iframe Hs; ipureintro; exact he
  · isplitl [Hf Hfd Hoff Hk Hm Hb Hv]
    · iframe Hf Hoff Hk
      isplitl [Hfd]
      · iexists rd; iexact Hfd
      iexists m, bs
      iframe Hm Hb
      isplitr
      · ipureintro; exact hp
      · iapply tailVar_unfold $$ Hv
    · iright; ipureintro; exact he

/-- **A window's tail synced is exact** (`OsMeta.synced`: `lo = hi = size`). -/
theorem TailMetaW.synced {m : OsMeta} {bs : List ByteG} (h : TailMetaW m bs) :
    TailMeta m.synced (bs.map (fun x => durB x.1)) :=
  ⟨by simp [OsMeta.synced, h.1], h.2.1, h.2.2.1.synced, rfl, rfl, PastZ.synced m⟩

/-- **`fileutil.Fdatasync` of the tail in a resize window** (`wp_tail` over `walTailW`'s `TailMetaW`): on
success the tail is exact again (`TailMeta` of the synced `OsMeta`, `TailMetaW.synced`). -/
theorem fileutil.Fdatasync.wp_tailW (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64)
    (name dir : GoString) (γ : GName) (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (hwr : o0 + out.length = (tailStream Mr H md cuts).length) :
    {{ walAreaOk walCodec Mr R jr r ∗
        walTailW (W := W) f fd name dir γ i H md cuts o0 sz out (tm := TailMetaW) ∗
        walCutFrag (W := W) none }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
    {{ (e : w64), RET #(errnoErr e); walCutFrag (W := W) none ∗
        ((⌜e = 0⌝ ∗ walTailW (W := W) f fd name dir γ i H md cuts o0 sz out ∗
            walSyncedLb (W := W) dir H.length) ∨
         (⌜e ≠ 0⌝ ∗ walTailW (W := W) f fd name dir γ i H md cuts o0 sz out (tm := TailMetaW))) }} := by
  wp_start as ⟨#Harea, Hw, Hcf⟩
  unfold walTailW
  icases Hw with ⟨Hf, ⟨%rd, Hfd⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  wp_auto
  wp_apply wp_Fd f fd name (DFrac.own 1) $$ Hf as Hf
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0 + out.length, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  wp_apply syscall.Fdatasync.wp_tail Mr R jr r dir γ H md cuts (o0 + out.length) m bs fd
    (DFrac.own 1) ⟨i, rd, true⟩ hp.2.1 hwr $$ [Harea Hfd Hk Hv Hcf Hm Hb]
    as %e ⟨Hfd, Hk, Hv, Hcf, Hr⟩
  · iframe; iexact Harea
  iapply HΦ
  iframe Hcf
  icases Hr with (⟨%he, Hm, Hb, #Hs⟩ | ⟨%he, Hm, Hb⟩)
  · ileft
    isplitr
    · ipureintro; exact he
    isplitl [Hf Hfd Hoff Hk Hm Hb Hv]
    · iframe Hf Hoff Hk
      isplitl [Hfd]
      · iexists rd; iexact Hfd
      iexists m.synced, (bs.map (fun x => durB x.1))
      iframe Hm Hb
      isplitr
      · ipureintro
        exact ⟨by simp [OsMeta.synced, hp.1], hp.2.1.synced, hp.2.2.1, hp.2.2.2.1, LoWr.of_exact rfl rfl⟩
      · iapply tailVar_unfold $$ Hv
    · iexact Hs
  · iright
    isplitr
    · ipureintro; exact he
    · iframe Hf Hoff Hk
      isplitl [Hfd]
      · iexists rd; iexact Hfd
      iexists m, bs
      iframe Hm Hb
      isplitr
      · ipureintro; exact hp
      · iapply tailVar_unfold $$ Hv

end tail

end WalFs
end EtcdGrove
end Perennial

end
