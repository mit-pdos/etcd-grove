/- Lean-first (no Rocq counterpart).

# `fileutil.Fdatasync` of the WAL's lent tail after `ZeroToEnd` (I3b, `wal-tc20`)

`Fdatasync.wp_specWalPend`: `Fdatasync.specWalPend` (`ReadAllTailCallees.lean`) over `os.File.Fd`, as
`fileutil.Fdatasync.wp_tail` (`TailFdatasync.lean`) but by the lent token of kind `false` (`walTailP`):

* `Fs.wp_osMeta_zfGe` (`MetaZf.lean`): before any step, the zeros known past an `OsMeta` start at or past its size
  (`MetaOk.zf`, a fact of the state): what the invariant's sync step needs of the tail (`hzf`), which
  `TailMetaZ` does not carry (`ZeroToEnd`'s post: the page cache fact only, `wal-tc19`).
* `wp_tailFsyncP`: `wp_tailFsync` over `walInvBody_syncP` (`TailSyncPend.lean`): the handle's zeros from
  the write position on (`ZeroToEnd`'s post) give the window's `WinZero`; on success the key back
  (`walLentRes_unpend` at the commit), the tail synced; on failure the token back.
* `syscall.Fdatasync.wp_tailP`, `fileutil.Fdatasync.wp_specWalPend`: the post's `TailMeta` of the synced
  `OsMeta` (`TailZ.synced_of` from `TailMetaZ`'s page cache fact, `PastZ.synced`, `LoWr.of_exact`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncPend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailFdatasync
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllTailCallees
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.MetaZf

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

/-- **The lent tail's fdatasync** (see the file header). -/
theorem wp_tailFsyncP (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (m : OsMeta) (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd) (Φ : val → IProp GF)
    (hm : TailMetaZ m bs) (hzw : ∀ b x, wr ≤ b → bs[b]? = some x → x.1 = 0)
    (hzf : ∀ z, m.zf = some z → m.size ≤ z) (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ osFd fd dq d -∗ walLentTokB (W := W) dir γ k false -∗
      tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
      osMeta d.ino (DFrac.own (1 : Qp).half) m -∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (∀ e : w64, osFd fd dq d -∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
        ((⌜e = 0⌝ ∗ walTailKey (W := W) dir γ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) ∗
            walSyncedLb (W := W) dir H.length) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ walLentTokB (W := W) dir γ k false ∗
            osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  iintro #Harea Hfd Hk Hv Hcf Hm1 Hb1 HΦ
  unfold walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := (⊤ : CoPset) \ ↑walN) _ _ rfl)
  iintro Hnc
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_syncP walCodec walCodec_ok Mr R jr r s dir γ k _ $$ Hb Hk Hv Hcf with
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
  have hwz : WinZero lay g0 := fun b x hb hx => hzw b x (by omega) hx
  imod (fupd_mask_subseteq (show (⊤ : CoPset) \ ↑walN ⊆ (⊤ : CoPset) \ ↑walN from fun _ h => h)) with Hid
  imodintro
  iframe Hnc
  iapply wp_osFsync fd dq d g0.om 0 g0.bs (OsMeta.covers_whole _ hm.1) osN_sub_nwal $$ Hos Hfd Hm Hbw
  iintro %e Hr Hfd
  icases Hr with (⟨%he, Hm, Hb⟩ | ⟨%he, Hm, Hb⟩)
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases Hconts with ⟨Hsucc, -⟩
    imod Hsucc $$ [] [Hm2 Hb2] with ⟨Hb, Hpast, Hk⟩
    · ipureintro; exact ⟨rfl, htail, hzf', hwz⟩
    · dsimp only [syncTail]; rw [← hino]; iframe
    imod Hid
    imod Hcl $$ [Hb]
    · iexists _; iexact Hb
    imodintro
    iapply HΦ $$ %e Hfd Hv Hcf
    ileft
    iframe
    isplitr
    · ipureintro; exact he
    unfold walSyncedLb
    iexists (walSyncS s dir dw), { dw with m := dw.H.length }
    iframe Hpast
    ipureintro
    exact ⟨walSyncS_lookup s dir dw, by rw [hH]; exact Nat.le_refl _⟩
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

/-- **`syscall.Fdatasync` of the lent tail** (see the file header). -/
theorem syscall.Fdatasync.wp_tailP (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (m : OsMeta) (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd)
    (hm : TailMetaZ m bs) (hzw : ∀ b x, wr ≤ b → bs[b]? = some x → x.1 = 0)
    (hzf : ∀ z, m.zf = some z → m.size ≤ z) (hwr : wr = (tailStream Mr H md cuts).length) :
    {{ walAreaOk walCodec Mr R jr r ∗ osFd fd dq d ∗ walLentTokB (W := W) dir γ k false ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! syscall.Fdatasync)) (Val #fd))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        ((⌜e = 0⌝ ∗ walTailKey (W := W) dir γ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) ∗
            walSyncedLb (W := W) dir H.length) ∨
         (⌜e ≠ 0⌝ ∗ walLentTokB (W := W) dir γ k false ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) }} := by
  wp_start as ⟨#Harea, Hfd, Hk, Hv, Hcf, Hm, Hb⟩
  try wp_auto
  wp_stub syscall.fsFsync.impl
  wp_apply wp_tailFsyncP Mr R jr r dir γ k H md cuts wr m bs fd dq d _ hm hzw hzf hwr
    $$ Harea Hfd Hk Hv Hcf Hm Hb as %e Hfd Hv Hcf Hr
  try wp_auto
  wp_apply wp_errnoErr
  try wp_auto
  iapply HΦ
  iframe Hfd Hv Hcf
  icases Hr with (⟨%he, Hr⟩ | ⟨%he, Hr⟩)
  · ileft; iframe Hr; ipureintro; exact he
  · iright; iframe Hr; ipureintro; exact he.1

/-- `TailMeta` of the synced tail after `ZeroToEnd` (`TailZ.synced_of` from `TailMetaZ`'s page cache
fact). -/
theorem TailMetaZ.synced {m : OsMeta} {bs : List ByteG} (h : TailMetaZ m bs) :
    TailMeta m.synced (bs.map (fun x => durB x.1)) :=
  ⟨by simp [OsMeta.synced, h.1], h.2.1, TailZ.synced_of h.2.2, rfl, rfl, PastZ.synced m⟩

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

/-- **`fileutil.Fdatasync` of the zeroed lent tail** (see the file header): `Fdatasync.specWalPend`. -/
theorem go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.wp_specWalPend
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG)) (Mr : WalMarshal) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.specWalPend (hG := hG) (W := W) Mr := by
  intro R jr r f fd name dir γ i H md cuts o0 sz k hS
  wp_start as ⟨#Harea, Hw, Hcf⟩
  unfold walTailP
  icases Hw with ⟨Hf, ⟨%rd, %lo, %lk, Hfd, Hlkt⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  obtain ⟨hmsz, ⟨hmz, hz⟩, hsz62, hfd, hlw⟩ := hp
  iapply Fs.wp_osMeta_zfGe _ _ rfl i _ m $$ Hm
  iintro %hzf Hm
  wp_auto
  wp_apply wp_Fd f fd name (DFrac.own 1) $$ Hf as Hf
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0 + ([] : List w8).length, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  wp_apply syscall.Fdatasync.wp_tailP Mr R jr r dir γ k H md cuts (o0 + ([] : List w8).length) m bs fd
    (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ hmz (fun b x hb hx => hz b x (by simpa using hb) hx) hzf
    (by simpa using hS) $$ [Harea Hfd Hk Hv Hcf Hm Hb]
    as %e ⟨Hfd, Hv, Hcf, Hr⟩
  · iframe; iexact Harea
  iapply HΦ
  iframe Hcf
  icases Hr with (⟨%he, Hk, Hm, Hb, #Hs⟩ | ⟨%he, Hk, Hm, Hb⟩)
  · ileft
    isplitr
    · ipureintro; exact he
    isplitl [Hf Hfd Hlkt Hoff Hk Hm Hb Hv]
    · unfold walTailW
      iframe Hf Hoff Hk
      isplitl [Hfd Hlkt]
      · iexists rd, lo, lk; iframe
      iexists m.synced, (bs.map (fun x => durB x.1))
      iframe Hm Hb
      isplitr
      · ipureintro
        refine ⟨by simp [OsMeta.synced, hmsz], ⟨hmz.synced, fun y hy => ?_⟩, hsz62, hfd, LoWr.of_exact rfl rfl⟩
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
      · iapply tailVar_unfold $$ Hv
    · iexact Hs
  · iright
    isplitr
    · ipureintro; exact he
    iframe Hf Hoff Hk
    isplitl [Hfd Hlkt]
    · iexists rd, lo, lk; iframe
    iexists m, bs
    iframe Hm Hb
    isplitr
    · ipureintro; exact ⟨hmsz, ⟨hmz, hz⟩, hsz62, hfd, by simpa using hlw⟩
    · iapply tailVar_unfold $$ Hv

end spec

end EtcdGrove
end Perennial

end
