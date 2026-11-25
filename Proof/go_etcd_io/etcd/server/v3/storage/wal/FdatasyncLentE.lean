/- Lean-first (no Rocq counterpart).

# `fileutil.Fdatasync` of the tail a failed `ZeroToEnd` left (unit `synclent`)

`Fdatasync.wp_specWalLentE`: `Fdatasync.specWalLentE` (`Spec/…/wal/FdatasyncLentE.lean`) over `os.File.Fd`, as
`Fdatasync.wp_specWalPend` (`FdatasyncPend.lean`) but from `walTailPE` (`TailMetaE`: the reader's stop at the write
position, `PendStop`) and over `walInvBody_syncPE` (`TailSyncPendE.lean`): on
success the token kept (its `|old|` the synced layout's), the tail synced (`TailMetaR` of the synced `OsMeta`,
every byte durable, the zeros known from the size on); on failure everything back.

* `wp_tailFsyncPE`: the fdatasync's atomic step on the invariant;
* `syscall.Fdatasync.wp_tailPE`, `fileutil.Fdatasync.wp_specWalLentE`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncPendE
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.FdatasyncPend
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.FdatasyncLentE

@[expose] public section

noncomputable section

set_option autoImplicit false

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

/-- **The fdatasync of the tail a failed `ZeroToEnd` left** (see the file header). -/
theorem wp_tailFsyncPE (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (p : Bool) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (m : OsMeta) (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd) (Φ : val → IProp GF)
    (hm : TailMetaE Mr (tailCrc Mr H md cuts) wr m bs)
    (hzf : ∀ z, m.zf = some z → m.size ≤ z) (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ osFd fd dq d -∗ walLentTokB (W := W) dir γ k p -∗
      tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
      osMeta d.ino (DFrac.own (1 : Qp).half) m -∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (∀ e : w64, osFd fd dq d -∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
        ((⌜e = 0⌝ ∗ (∃ k' : Nat, walLentTokB (W := W) dir γ k' p) ∗
            osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1))) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ walLentTokB (W := W) dir γ k p ∗
            osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  iintro #Harea Hfd Hk Hv Hcf Hm1 Hb1 HΦ
  unfold walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := (⊤ : CoPset) \ ↑walN) _ _ rfl)
  iintro Hnc
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_syncPE walCodec walCodec_ok Mr R jr r s dir γ k p _ $$ Hb Hk Hv Hcf with
    ⟨%F, %dw, %lay, %pre, %g0, %hp, Hseg, Hv, Hcf, Hconts⟩
  obtain ⟨hdw, hs, htg, ⟨ents, habs⟩⟩ := hp
  simp only [tailG, Prod.mk.injEq] at htg
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htg
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨hsz, -, -, -, -⟩ := habs.metas g0 (List.mem_of_getLast? hg0)
  unfold segResF segRes
  rw [← hF]
  dsimp only
  icases Hseg with ⟨Hm2, Hb2⟩
  rw [← hino]
  icases osMeta_agree' _ _ _ _ _ $$ Hm1 Hm2 with %hmm
  subst hmm
  icases osBytes_agree d.ino _ _ 0 bs g0.bs (by rw [hm.1, hsz]) $$ Hb1 Hb2 with %hbb
  subst hbb
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  ihave Hbw := (osBytes_halves _ _ _).2 $$ [Hb1 Hb2]
  · iframe
  have htail : lay.wr = (segStream walCodec Mr dw lay.cuts lay.cuts.length).length := by
    rw [← hwrl, hwr, hH, hmd, hcuts]; rfl
  have hzf' : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z := fun z hz => by
    rw [hm.1]; exact hzf z hz
  have hpv : PendStop walCodec Mr (g0.bs.map (·.1)) lay.wr
      (WalEnc.chainEnd walCodec 0#32 (recsOfSegs walCodec Mr dw.metadata (segsOf (histM dw) lay.cuts))) := by
    rw [← hwrl, ← hcuts, ← hmd, show histM dw = histN H by rw [histM, hH]]; exact hm.2.2.2
  imod (fupd_mask_subseteq (show (⊤ : CoPset) \ ↑walN ⊆ (⊤ : CoPset) \ ↑walN from fun _ h => h)) with Hid
  imodintro
  iframe Hnc
  iapply wp_osFsync fd dq d g0.om 0 g0.bs (OsMeta.covers_whole _ hm.1) osN_sub_nwal $$ Hos Hfd Hm Hbw
  iintro %e Hr Hfd
  icases Hr with (⟨%he, Hm, Hb⟩ | ⟨%he, Hm, Hb⟩)
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases Hconts with ⟨Hsucc, -⟩
    imod Hsucc $$ [] [Hm2 Hb2] with ⟨Hb, -, Hk⟩
    · ipureintro; exact ⟨rfl, htail, hzf', hpv⟩
    · dsimp only [syncTail]; rw [← hino]; iframe
    imod Hid
    imod Hcl $$ [Hb]
    · iexists _; iexact Hb
    imodintro
    iapply HΦ $$ %e Hfd Hv Hcf
    ileft
    iframe
    ipureintro; exact he
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases Hconts with ⟨-, Hfail⟩
    ihave ⟨Hb, Hk⟩ := Hfail $$ [Hm2 Hb2]
    · iframe
    imod Hid
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    iapply HΦ $$ %e Hfd Hv Hcf
    iright
    iframe
    ipureintro; exact he

variable [syscall_sem : syscall.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`syscall.Fdatasync` of the tail a failed `ZeroToEnd` left** (see the file header). -/
theorem syscall.Fdatasync.wp_tailPE (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (m : OsMeta) (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd)
    (hm : TailMetaE Mr (tailCrc Mr H md cuts) wr m bs)
    (hzf : ∀ z, m.zf = some z → m.size ≤ z) (hwr : wr = (tailStream Mr H md cuts).length) :
    {{ walAreaOk walCodec Mr R jr r ∗ osFd fd dq d ∗ walLentTokB (W := W) dir γ k false ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! syscall.Fdatasync)) (Val #fd))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        ((⌜e = 0⌝ ∗ (∃ k' : Nat, walLentTokB (W := W) dir γ k' false) ∗
            osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1))) ∨
         (⌜e ≠ 0⌝ ∗ walLentTokB (W := W) dir γ k false ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) }} := by
  wp_start as ⟨#Harea, Hfd, Hk, Hv, Hcf, Hm, Hb⟩
  wp_apply wp_tailFsyncPE Mr R jr r dir γ k false H md cuts wr m bs fd dq d _ hm hzf hwr
    $$ Harea Hfd Hk Hv Hcf Hm Hb as %e Hfd Hv Hcf Hr
  iapply wp_errno
  iapply HΦ
  iframe Hfd Hv Hcf
  icases Hr with (⟨%he, Hr⟩ | ⟨%he, Hr⟩)
  · ileft; iframe Hr; ipureintro; exact he
  · iright; iframe Hr; ipureintro; exact he.1

end tail

end WalFs

section spec
open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc WalFs

variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [syscall_sem : syscall.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`fileutil.Fdatasync` of the tail a failed `ZeroToEnd` left** (see the file header):
`Fdatasync.specWalLentE`. -/
theorem go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.wp_specWalLentE
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG)) (Mr : WalMarshal) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.specWalLentE (hG := hG) (W := W) Mr := by
  intro R jr r f fd name dir γ i H md cuts o0 k hS
  wp_start as ⟨#Harea, Hw, Hcf⟩
  unfold walTailPE
  icases Hw with ⟨Hf, ⟨%rd, %lo, %lk, Hfd, Hlkt⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  obtain ⟨hfd, hmE⟩ := hp
  iapply Fs.wp_osMeta_zfGe _ _ rfl i _ m $$ Hm
  iintro %hzf Hm
  wp_auto
  wp_apply wp_Fd f fd name (DFrac.own 1) $$ Hf as Hf
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  wp_apply syscall.Fdatasync.wp_tailPE Mr R jr r dir γ k H md cuts o0 m bs fd
    (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ hmE hzf hS $$ [Harea Hfd Hk Hv Hcf Hm Hb]
    as %e ⟨Hfd, Hv, Hcf, Hr⟩
  · iframe; iexact Harea
  iapply HΦ
  iframe Hcf
  icases Hr with (⟨%he, Hk, Hm, Hb⟩ | ⟨%he, Hk, Hm, Hb⟩)
  · ileft
    isplitr
    · ipureintro; exact he
    iframe Hf Hoff Hk Hv
    isplitl [Hfd Hlkt]
    · iexists rd, lo, lk; iframe
    iexists m.synced, (bs.map (fun x => durB x.1))
    iframe Hm Hb
    ipureintro
    refine ⟨⟨by simp [OsMeta.synced, hmE.1], hmE.2.1, rfl, rfl⟩, fun z hz => ?_, fun y hy => ?_⟩
    · simp only [OsMeta.synced, Option.some.injEq] at hz
      rw [← hz]; exact OsMeta.size_le_syncZ m
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
  · iright
    isplitr
    · ipureintro; exact he
    iframe Hf Hoff Hk
    isplitl [Hfd Hlkt]
    · iexists rd, lo, lk; iframe
    iexists m, bs
    iframe Hm Hb
    isplitr
    · ipureintro; exact ⟨hfd, hmE⟩
    · iapply tailVar_unfold $$ Hv

end spec

end EtcdGrove
end Perennial

end
