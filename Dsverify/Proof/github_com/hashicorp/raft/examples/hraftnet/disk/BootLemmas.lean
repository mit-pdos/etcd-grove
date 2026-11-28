/-
(hraft_robust R3) The disk invariant's allocation, the generation's start (`DISKCRASH.md`):

* `disk_boot`: from `durable`'s state holding an image's encoding (what `Open` read), a fresh generation's
  names, its invariant idle at the image, the crash token, the client views (staged `0`) and the record's
  other half (for the lock invariant);
* `disk_boot_fresh`: from any state of the file and the caller's `Wf`, the same at the empty image, in the
  `fresh` window (the first start's `Fresh`, which writes the empty image);
* `freshWriteAU`: `Fresh`'s `durable.Write` updates: the rename records that the file holds the empty image,
  the sync closes the window idle and gives `Wf` back.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.WriteLemmas

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode Iris.Std github_com.hashicorp.raft proto EtcdGrove

/-- The empty image (what `Fresh` writes). -/
def emptyImg : DiskImg := ⟨[], [], [], W64 0⟩

theorem emptyImg_ok : emptyImg.Ok := by
  refine ⟨trivial, List.nodup_nil, List.nodup_nil, ?_, ?_, ?_, ?_⟩ <;> simp [emptyImg]

theorem emptyImg_absL : emptyImg.absL (W64 0) = LogAbs.empty := rfl

theorem emptyImg_absS : emptyImg.absS = ⟨∅, ∅⟩ := rfl

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **A generation's start from the file's image** (see the file header). -/
theorem disk_boot (γd : DurFs.DurGS) (f : DurFs.DFile) (R : Fs.Roots) (Wl : LogOp → IProp GF)
    (Ws : StableOp → IProp GF) (Wf : IProp GF) (I : DiskImg) (hok : I.Ok) (E : CoPset) :
    ⊢ DurFs.durSt γd ⟨some (encImg I), none⟩ ={E}=∗ ∃ g : DiskGen,
      ⌜g.γd = γd ∧ g.f = f ∧ g.R = R⌝ ∗ diskInv g Wl Ws Wf ∗ token g.γk ∗
      diskOwnL g (I.absL (W64 0)) ∗ diskOwnS g I.absS ∗
      ghostVar g.γw (1 : Qp).half ((I, W64 0, DiskWin.idle) : DiskRec) := by
  iintro Hds
  imod ghostVar_alloc (GF := GF) (I.absL (W64 0)) with ⟨%γl, Hl⟩
  imod ghostVar_alloc (GF := GF) I.absS with ⟨%γs, Hs⟩
  imod ghostVar_alloc (GF := GF) ((I, W64 0, DiskWin.idle) : DiskRec) with ⟨%γw, Hw⟩
  imod token_alloc (GF := GF) with ⟨%γk, Hk⟩
  icases ghostVar_halves γl _ $$ Hl with ⟨Hl1, Hl2⟩
  icases ghostVar_halves γs _ $$ Hs with ⟨Hs1, Hs2⟩
  icases ghostVar_halves γw _ $$ Hw with ⟨Hw1, Hw2⟩
  imod inv_alloc diskN E (diskBody (⟨γd, f, R, γl, γs, γw, γk⟩ : DiskGen) Wl Ws Wf) $$ [Hds Hl1 Hs1 Hw1] with #Hinv
  · inext; iunfold diskBody; iexists I, W64 0, DiskWin.idle, ⟨some (encImg I), none⟩
    iframe; ileft; iframe; simp only [diskWinRes]; ipureintro; exact ⟨hok, by first | rfl | trivial⟩
  imodintro
  iexists ⟨γd, f, R, γl, γs, γw, γk⟩
  unfold diskOwnL diskOwnS diskInv
  iframe; iframe #
  ipureintro; exact ⟨rfl, rfl, rfl⟩

/-- **The first start's generation**, before `Fresh` writes the empty image. -/
theorem disk_boot_fresh (γd : DurFs.DurGS) (f : DurFs.DFile) (R : Fs.Roots) (Wl : LogOp → IProp GF)
    (Ws : StableOp → IProp GF) (Wf : IProp GF) (s : DurFs.DurSt) (E : CoPset) :
    ⊢ DurFs.durSt γd s -∗ Wf ={E}=∗ ∃ g : DiskGen,
      ⌜g.γd = γd ∧ g.f = f ∧ g.R = R⌝ ∗ diskInv g Wl Ws Wf ∗ token g.γk ∗
      diskOwnL g LogAbs.empty ∗ diskOwnS g ⟨∅, ∅⟩ ∗
      ghostVar g.γw (1 : Qp).half ((emptyImg, W64 0, DiskWin.fresh false) : DiskRec) := by
  iintro Hds HWf
  imod ghostVar_alloc (GF := GF) (emptyImg.absL (W64 0)) with ⟨%γl, Hl⟩
  imod ghostVar_alloc (GF := GF) emptyImg.absS with ⟨%γs, Hs⟩
  imod ghostVar_alloc (GF := GF) ((emptyImg, W64 0, DiskWin.fresh false) : DiskRec) with ⟨%γw, Hw⟩
  imod token_alloc (GF := GF) with ⟨%γk, Hk⟩
  icases ghostVar_halves γl _ $$ Hl with ⟨Hl1, Hl2⟩
  icases ghostVar_halves γs _ $$ Hs with ⟨Hs1, Hs2⟩
  icases ghostVar_halves γw _ $$ Hw with ⟨Hw1, Hw2⟩
  imod inv_alloc diskN E (diskBody (⟨γd, f, R, γl, γs, γw, γk⟩ : DiskGen) Wl Ws Wf) $$ [Hds Hl1 Hs1 Hw1 HWf]
    with #Hinv
  · inext; iunfold diskBody; iexists emptyImg, W64 0, DiskWin.fresh false, s
    iframe; ileft; iframe; simp only [diskWinRes]; iframe
    ipureintro; exact ⟨emptyImg_ok, by first | trivial | (intro h; cases h)⟩
  imodintro
  iexists ⟨γd, f, R, γl, γs, γw, γk⟩
  unfold diskOwnL diskOwnS diskInv
  iframe; iframe #
  ipureintro; exact ⟨rfl, rfl, rfl⟩

/-- **`Fresh`'s `durable.Write` updates** (see the file header). -/
theorem freshWriteAU (g : DiskGen) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (P : IProp GF) :
    ⊢ diskInv g Wl Ws Wf -∗ ghostVar g.γw (1 : Qp).half ((emptyImg, W64 0, DiskWin.fresh false) : DiskRec) -∗
      £ 1 -∗ (ghostVar g.γw (1 : Qp).half ((emptyImg, W64 0, DiskWin.idle) : DiskRec) -∗ Wf -∗ P) -∗
      (⌜(encImg emptyImg).length < 2 ^ 63⌝ -∗
        AU <{ ∃∃ s : DurFs.DurSt, DurFs.durSt (GF := GF) g.γd s }> @ DurFs.durAuMask, ∅
          <{ DurFs.durSt (GF := GF) g.γd ⟨some (encImg emptyImg), some s.cur⟩, COMM
            DurFs.durWriteSync (GF := GF) g.γd P }>) := by
  iintro #Hinv Hrec Hlc HK %_
  iauintro
  unfold atomic_acc
  iunfold diskInv at Hinv
  imod inv_acc (E := DurFs.durAuMask) diskN_sub_durAu $$ Hinv with ⟨Hi, Hclose⟩
  iunfold diskBody at Hi
  imod later_exists_except0 $$ Hi with ⟨%I0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%stg0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%w0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%s0, Hi⟩
  icases Hi with ⟨Hds, Hrec0, Hb⟩
  imod Hds
  imod Hrec0
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑diskN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists s0
  iframe Hds
  isplit
  · iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hrec0 Hb] with -
    · inext; iunfold diskBody; iexists emptyImg, W64 0, DiskWin.fresh false, s0; iframe
    imodintro
    iframe
  iintro Hds
  imod Hclose2 with -
  imod ghostVar_update_halves ((emptyImg, W64 0, DiskWin.fresh true) : DiskRec) g.γw _ _ $$ Hrec Hrec0
    with ⟨Hrec, Hrec0⟩
  ihave Hb' : iprop(▷ ((ghostVar g.γl (1 : Qp).half (emptyImg.absL (W64 0)) ∗ ghostVar g.γs (1 : Qp).half emptyImg.absS ∗
      ⌜emptyImg.Ok⌝ ∗ diskWinRes Wl Ws Wf emptyImg (W64 0) ⟨some (encImg emptyImg), some s0.cur⟩ (DiskWin.fresh true)) ∨
      crashed ∗ token g.γk)) $$ [Hb]
  · icases later_or.1 $$ Hb with (Hb | Hb)
    · inext
      ileft
      icases Hb with ⟨Hl, Hs, %Hok, Hwin⟩
      simp only [diskWinRes]
      icases Hwin with ⟨HWf, -⟩
      iframe
      ipureintro; exact ⟨Hok, by first | trivial | (intro _; rfl)⟩
    · inext; iright; iexact Hb
  imod Hclose $$ [Hds Hrec0 Hb'] with -
  · inext; iunfold diskBody; iexists emptyImg, W64 0, DiskWin.fresh true, ⟨some (encImg emptyImg), some s0.cur⟩
    iframe
  imodintro
  -- the sync: the window closes idle, `Wf` comes back
  iintro Hnc
  iauintro
  unfold atomic_acc
  imod inv_acc (E := DurFs.durAuMask) diskN_sub_durAu $$ Hinv with ⟨Hi, Hclose⟩
  iunfold diskBody at Hi
  imod later_exists_except0 $$ Hi with ⟨%I1, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%stg1, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%w1, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%s1, Hi⟩
  icases Hi with ⟨Hds, Hrec0, Hb⟩
  imod Hds
  imod Hrec0
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  imod notCrashed_or_crashed $$ [$Hnc $Hb] with ⟨Hnc, Hb⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑diskN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists s1
  iframe Hds
  isplit
  · iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hrec0 Hb] with -
    · inext; iunfold diskBody; iexists emptyImg, W64 0, DiskWin.fresh true, s1; iframe
    imodintro
    iframe
  iintro Hds
  imod Hclose2 with -
  imod lc_fupd_elim_later $$ Hlc Hb with Hb
  icases Hb with ⟨Hl, Hs, %Hok, Hwin⟩
  simp only [diskWinRes]
  icases Hwin with ⟨HWf, %Hr⟩
  have hcur := Hr trivial
  imod ghostVar_update_halves ((emptyImg, W64 0, DiskWin.idle) : DiskRec) g.γw _ _ $$ Hrec Hrec0
    with ⟨Hrec, Hrec0⟩
  imod Hclose $$ [Hds Hrec0 Hl Hs] with -
  · inext; iunfold diskBody; iexists emptyImg, W64 0, DiskWin.idle, ⟨s1.cur, none⟩
    iframe; ileft; iframe; simp only [diskWinRes]; ipureintro; refine ⟨Hok, ?_⟩; first | trivial | rfl | rw [hcur]
  imodintro
  iframe Hnc
  iapply HK $$ Hrec HWf

end lemmas

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
