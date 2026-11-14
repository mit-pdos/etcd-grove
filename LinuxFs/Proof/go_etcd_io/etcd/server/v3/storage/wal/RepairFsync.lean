/- Lean-first (no Rocq counterpart).

# `fileutil.Fsync` of `Repair`'s truncated tail (L4; the W7-W12 log, thirteenth session)

`fileutil.Fsync.wp_specRepTail`: `Fsync.specRepTail` (`RepairCallees.lean`) over the body of `os.File.Sync`
(the part's model: the fd's kind, then the extension's `Fsync`, `EINTR` retried), as
`Fdatasync.wp_specWalPend` (`FdatasyncPend.lean`) by the pending token (kind `true`):

* `wp_tailFsyncR`: `wp_tailFsyncP` over `walInvBody_syncR` (`RepairSync.lean`): the segment `wr` long
  (the truncate landed) in place of the handle's zeros from `wr` on; on success the key back (the
  synced layout has F-Z), the tail synced; on failure the token back.
* `os.File.Sync.wp_tailR`: `os.File.Sync.wp_proof` (`LinuxFs/Proof/os/File__Sync.lean`) with the tail's
  step for `wp_osFsync` (never `EINTR`).
* `fileutil.Fsync.wp_specRepTail`: the zeros known past the size first (`Fs.wp_osMeta_zfGe`), then the
  above; the post's `TailMeta` of the synced `OsMeta` (`TailZ.synced_of` from the page cache fact the
  landed truncate leaves, `PastZ.synced`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairSync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.FdatasyncPend
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.RepairCallees
public import LinuxFs.Proof.os.ErrorOk
public import LinuxFs.Spec.os.File__Sync

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

/-- **The fsync step of `Repair`'s truncated tail** (`wp_tailFsyncP` by the pending token over
`walInvBody_syncR`; see the file header). -/
theorem wp_tailFsyncR (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (m : OsMeta) (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd) (Φ : val → IProp GF)
    (hm : TailMetaRW m bs) (hlen : m.size ≤ wr)
    (hzf : ∀ z, m.zf = some z → m.size ≤ z) (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ osFd fd dq d -∗ walLentTokB (W := W) dir γ k true -∗
      tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
      osMeta d.ino (DFrac.own (1 : Qp).half) m -∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (∀ e : w64, osFd fd dq d -∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
        ((⌜e = 0⌝ ∗ walTailKey (W := W) dir γ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) ∗
            walSyncedLb (W := W) dir H.length) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ walLentTokB (W := W) dir γ k true ∗
            osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  iintro #Harea Hfd Hk Hv Hcf Hm1 Hb1 HΦ
  unfold walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := (⊤ : CoPset) \ ↑walN) _ _ rfl)
  iintro Hnc
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_syncR walCodec walCodec_ok Mr R jr r s dir γ k _ $$ Hb Hk Hv Hcf with
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
  have hlen' : g0.bs.length ≤ lay.wr := by rw [hm.1, ← hwrl]; exact hlen
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
    · ipureintro; exact ⟨rfl, htail, hzf', hlen'⟩
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

/-- The area's `osInv`. -/
theorem walAreaOk_osInv (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    walAreaOk (L := hG.goose_localGS) (W := W) C Mr R jr r ⊢ osInv (L := hG.goose_localGS) := by
  unfold walAreaOk
  iintro ⟨-, #H, -⟩
  iexact H

/-- **`f.Sync()` of `Repair`'s truncated tail** (`os.File.Sync.wp_proof` with `wp_tailFsyncR` for the
extension's step; see the file header). -/
theorem os.File.Sync.wp_tailR (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (m : OsMeta) (bs : List ByteG) (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd)
    (hm : TailMetaRW m bs) (hlen : m.size ≤ wr) (hzf : ∀ z, m.zf = some z → m.size ≤ z)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    {{ walAreaOk walCodec Mr R jr r ∗ os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        walLentTokB (W := W) dir γ k true ∗ tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗
        walCutFrag (W := W) none ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        ((⌜err = interface.nil⌝ ∗ walTailKey (W := W) dir γ ∗
            osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1))) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  unfold os.ownFile
  wp_start as ⟨#Harea, ⟨%inner, #Hf, Hfo, #Hn⟩, Hosfd, Hk, Hv, Hcf, Hm, Hbs⟩
  ihave #Hos := walAreaOk_osInv walCodec Mr R jr r $$ Harea
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFdKind fd dq d CoPset.subseteq_top $$ Hos Hosfd as Hosfd
  wp_apply wp_tailFsyncR Mr R jr r dir γ k H md cuts wr m bs fd dq d _ hm hlen hzf hwr
    $$ Harea Hosfd Hk Hv Hcf Hm Hbs as %e Hosfd Hv Hcf Hr
  by_cases he4 : e = W64 4
  · icases Hr with (⟨%he, -⟩ | ⟨%he, -⟩)
    · exact absurd (he4 ▸ he) (by decide)
    · exact absurd he4 he.2
  rw [decide_eq_false he4]
  wp_auto
  icases Hr with (⟨%he, Hk, Hm, Hbs, -⟩ | ⟨%he, -⟩)
  · subst he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    ileft
    isplitr; · ipureintro; rfl
    iframe
  · have he0' : ¬ e = W64 0 := he.1
    simp only [decide_eq_false he0', Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn as %pe #Hok
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    iright
    ipureintro; intro h; cases h

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
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`fileutil.Fsync` of `Repair`'s truncated tail** (see the file header): `Fsync.specRepTail`. -/
theorem go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.wp_specRepTail (Mr : WalMarshal) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specRepTail (hG := hG) (W := W) Mr := by
  intro R jr r f fd name dir γ i H md cuts o0 k off hS
  wp_start as ⟨#Harea, Hw, Hcf⟩
  unfold walTailPO
  icases Hw with ⟨Hf, ⟨%rd, Hfd⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  obtain ⟨hmsz, hmz, hsz62, hfd, -⟩ := hp
  iapply Fs.wp_osMeta_zfGe _ _ rfl i _ m $$ Hm
  iintro %hzf Hm
  wp_auto
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  wp_apply WalFs.os.File.Sync.wp_tailR Mr R jr r dir γ k H md cuts o0 m bs f fd name (DFrac.own 1)
    (DFrac.own 1) ⟨i, rd, true⟩ hmz (by omega) hzf hS $$ [Harea Hf Hfd Hk Hv Hcf Hm Hb]
    as %err ⟨Hf, Hfd, Hv, Hcf, Hr⟩
  · iframe; iexact Harea
  iapply HΦ
  iframe Hcf Hf Hoff
  isplitl [Hfd]
  · iexists rd; iexact Hfd
  icases Hr with (⟨%he, Hk, Hm, Hb⟩ | %he)
  · ileft
    isplitr
    · ipureintro; exact he
    iframe Hk
    iexists m.synced, (bs.map (fun x => durB x.1))
    iframe Hm Hb
    isplitr
    · ipureintro
      refine ⟨by simp [OsMeta.synced, hmsz], ⟨by simp [OsMeta.synced, hmz.1], hmz.2.1, rfl, rfl⟩,
        fun z hz => ?_, fun y hy => ?_⟩
      · simp only [OsMeta.synced, Option.some.injEq] at hz
        rw [← hz]; exact OsMeta.size_le_syncZ m
      · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
    · iapply tailVar_unfold $$ Hv
  · iright; ipureintro; exact he

end spec

end EtcdGrove
end Perennial

end
