/-
(hraft_robust R3) A write of `dir/raft` over the disk's invariant (`DISKCRASH.md`, `PACKET.md` steps 2-4):

* `diskWriteAU`: `durable.Write`'s two atomic updates for a write `op` to the image `I'` (what `persist`
  takes). At the rename the window opens (`open op I' false`), `durSt` goes from the old image's encoding to
  `⟨enc I', some (enc I)⟩`, and the client's window resource moves into the invariant; at the sync `alt := none`
  and the record says so (`sy := true`).
* `diskCommitL`, `diskCommitS`: after `Write` returns, the window resource comes out and the client's atomic
  update runs with it; the views move to the write's result and the window closes idle at `I'`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.InvLemmas

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode Iris.Std github_com.hashicorp.raft proto EtcdGrove

/-- A log write's result. -/
def logApply : LogOp → LogAbs → LogAbs
  | .store first es, A => A.store first es
  | .del _ mn mx, A => A.delete mn mx (maxKey (LogAbs.del A.m mn mx))

/-- A stable write's result. -/
def stabApply : StableOp → StableAbs → StableAbs
  | .setU k v, S => { S with ints := S.ints.insert k v }
  | .set k vb, S => { S with bytes := S.bytes.insert k vb }

theorem apply_log (o : LogOp) (D : DiskAbs) : (DiskOp.log o).apply D = { D with L := logApply o D.L } := by
  cases o <;> rfl

theorem apply_stab (o : StableOp) (D : DiskAbs) : (DiskOp.stab o).apply D = { D with S := stabApply o D.S } := by
  cases o <;> rfl

theorem of_log (o : LogOp) (I I' : DiskImg) (stg : w64)
    (h : DiskAbs.of I' stg = (DiskOp.log o).apply (DiskAbs.of I stg)) :
    I'.absL stg = logApply o (I.absL stg) ∧ I'.absS = I.absS := by
  rw [apply_log] at h; unfold DiskAbs.of at h; simp only [DiskAbs.mk.injEq] at h; exact h

theorem of_stab (o : StableOp) (I I' : DiskImg) (stg : w64)
    (h : DiskAbs.of I' stg = (DiskOp.stab o).apply (DiskAbs.of I stg)) :
    I'.absL stg = I.absL stg ∧ I'.absS = stabApply o I.absS := by
  rw [apply_stab] at h; unfold DiskAbs.of at h; simp only [DiskAbs.mk.injEq] at h; exact h

theorem durSt_eta (s : DurFs.DurSt) (v : GoString) (h1 : s.cur = some v) (h2 : s.alt = none) :
    s = ⟨some v, none⟩ := by
  cases s; simp only at h1 h2; subst h1 h2; rfl

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **`durable.Write`'s atomic updates for a write** (see the file header). -/
theorem diskWriteAU (g : DiskGen) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (I I' : DiskImg) (stg : w64) (op : DiskOp) (P : IProp GF)
    (hpre : I'.Pre) (hab : DiskAbs.of I' stg = op.apply (DiskAbs.of I stg)) :
    ⊢ diskInv g Wl Ws Wf -∗ ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.idle) : DiskRec) -∗
      winOf Wl Ws op -∗
      (ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.open op I' true) : DiskRec) -∗ P) -∗
      (⌜(encImg I').length < 2 ^ 63⌝ -∗
        AU <{ ∃∃ s : DurFs.DurSt, DurFs.durSt (GF := GF) g.γd s }> @ DurFs.durAuMask, ∅
          <{ DurFs.durSt (GF := GF) g.γd ⟨some (encImg I'), some s.cur⟩, COMM DurFs.durWriteSync (GF := GF) g.γd P }>) := by
  iintro #Hinv Hrec Hw HK %hlen
  have hok' : I'.Ok := ok_of_enc I' hpre hlen
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
  · -- abort
    iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hrec0 Hb] with -
    · inext; iunfold diskBody; iexists I, stg, DiskWin.idle, s0; iframe
    imodintro
    iframe
  -- the rename
  iintro Hds
  imod Hclose2 with -
  imod ghostVar_update_halves ((I, stg, DiskWin.open op I' false) : DiskRec) g.γw _ _ $$ Hrec Hrec0
    with ⟨Hrec, Hrec0⟩
  ihave Hb' : iprop(▷ ((ghostVar g.γl (1 : Qp).half (I.absL stg) ∗ ghostVar g.γs (1 : Qp).half I.absS ∗ ⌜I.Ok⌝ ∗
      diskWinRes Wl Ws Wf I stg ⟨some (encImg I'), some s0.cur⟩ (DiskWin.open op I' false)) ∨
      crashed ∗ token g.γk)) $$ [Hb Hw]
  · icases later_or.1 $$ Hb with (Hb | Hb)
    · inext
      ileft
      icases Hb with ⟨Hl, Hs, %Hok, Hidle⟩
      simp only [diskWinRes]
      icases Hidle with %Hidle
      iframe Hl Hs Hw
      ipureintro
      subst Hidle
      refine ⟨Hok, hok', hab, ?_, ?_⟩ <;> simp
    · inext; iright; iexact Hb
  imod Hclose $$ [Hds Hrec0 Hb'] with -
  · inext; iunfold diskBody; iexists I, stg, DiskWin.open op I' false, ⟨some (encImg I'), some s0.cur⟩
    iframe
  imodintro
  -- the directory's sync
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
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑diskN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists s1
  iframe Hds
  isplit
  · iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hrec0 Hb] with -
    · inext; iunfold diskBody; iexists I, stg, DiskWin.open op I' false, s1; iframe
    imodintro
    iframe
  iintro Hds
  imod Hclose2 with -
  imod ghostVar_update_halves ((I, stg, DiskWin.open op I' true) : DiskRec) g.γw _ _ $$ Hrec Hrec0
    with ⟨Hrec, Hrec0⟩
  ihave Hb' : iprop(▷ ((ghostVar g.γl (1 : Qp).half (I.absL stg) ∗ ghostVar g.γs (1 : Qp).half I.absS ∗ ⌜I.Ok⌝ ∗
      diskWinRes Wl Ws Wf I stg ⟨s1.cur, none⟩ (DiskWin.open op I' true)) ∨
      crashed ∗ token g.γk)) $$ [Hb]
  · icases later_or.1 $$ Hb with (Hb | Hb)
    · inext
      ileft
      icases Hb with ⟨Hl, Hs, %Hok, Hwin⟩
      simp only [diskWinRes]
      icases Hwin with ⟨%Hf, Hw⟩
      iframe Hl Hs Hw
      ipureintro
      refine ⟨Hok, Hf.1, Hf.2.1, Hf.2.2.1, ?_⟩; simp
    · inext; iright; iexact Hb
  imod Hclose $$ [Hds Hrec0 Hb'] with -
  · inext; iunfold diskBody; iexists I, stg, DiskWin.open op I' true, ⟨s1.cur, none⟩
    iframe
  imodintro
  iframe Hnc
  iapply HK $$ Hrec

/-- **A log write's commit**, after `Write` returned (see the file header). -/
theorem diskCommitL (g : DiskGen) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (I I' : DiskImg) (stg : w64) (o : LogOp) (R : LogAbs → IProp GF) (Q : IProp GF) :
    ⊢ diskInv g Wl Ws Wf -∗ ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.open (.log o) I' true) : DiskRec) -∗
      £ 1 -∗ £ 1 -∗
      (∀ A, R A -∗ diskOwnL g (logApply o A) ={∅,⊤ \ ↑storeN}=∗ Q) -∗
      (Wl o -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, diskOwnL g A ∗ R A) -∗
      |NC={⊤}=> ghostVar g.γw (1 : Qp).half ((I', stg, DiskWin.idle) : DiskRec) ∗ ⌜I'.Ok⌝ ∗ Q := by
  iintro #Hinv Hrec Hlc1 Hlc2 HR HAU Hnc
  iunfold diskInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc1 Hb with Hb
  iunfold diskBody at Hb
  icases Hb with ⟨%I0, %stg0, %w0, %s0, Hds, Hrec0, Hb⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  icases Hb with (⟨Hl, Hs, %Hok, Hwin⟩ | ⟨Hc, -⟩)
  · simp only [diskWinRes]
    icases Hwin with ⟨%Hf, Hw⟩
    obtain ⟨hok', hab, hcur, halt⟩ := Hf
    have halt' : s0.alt = none := by
      rcases halt with h | ⟨h, _⟩; exact h; cases h
    obtain ⟨hL, hS⟩ := of_log o I I' stg hab
    imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤ \ ↑diskN) (E2 := ⊤ \ ↑storeN)
      diff_storeN_sub_diskN) with Hmask
    iunfold winOf at Hw
    imod HAU $$ Hw Hnc with ⟨Hnc, HAU⟩
    imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%A, Hown, HRA⟩
    iunfold diskOwnL at Hown
    ihave %HA := ghostVar_agree _ _ _ _ _ $$ Hown Hl
    subst HA
    imod ghostVar_update_halves (I'.absL stg) g.γl _ _ $$ Hown Hl with ⟨Hown, Hl⟩
    imod ghostVar_update_halves ((I', stg, DiskWin.idle) : DiskRec) g.γw _ _ $$ Hrec Hrec0 with ⟨Hrec, Hrec0⟩
    imod HR $$ HRA [Hown] with HQ
    · iunfold diskOwnL; rw [← hL]; iexact Hown
    imod Hmask with -
    imod Hclose $$ [Hds Hrec0 Hl Hs] with -
    · inext; iunfold diskBody; iexists I', stg, DiskWin.idle, s0; iframe Hds Hrec0; ileft; iframe Hl
      rw [hS]; iframe Hs
      simp only [diskWinRes]
      ipureintro; exact ⟨hok', durSt_eta s0 _ hcur halt'⟩
    imodintro; iframe; ipureintro; exact hok'
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

/-- **A stable write's commit**, after `Write` returned. -/
theorem diskCommitS (g : DiskGen) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (I I' : DiskImg) (stg : w64) (o : StableOp) (R : StableAbs → IProp GF) (Q : IProp GF) :
    ⊢ diskInv g Wl Ws Wf -∗ ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.open (.stab o) I' true) : DiskRec) -∗
      £ 1 -∗ £ 1 -∗
      (∀ S, R S -∗ diskOwnS g (stabApply o S) ={∅,⊤ \ ↑storeN}=∗ Q) -∗
      (Ws o -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ S, diskOwnS g S ∗ R S) -∗
      |NC={⊤}=> ghostVar g.γw (1 : Qp).half ((I', stg, DiskWin.idle) : DiskRec) ∗ ⌜I'.Ok⌝ ∗ Q := by
  iintro #Hinv Hrec Hlc1 Hlc2 HR HAU Hnc
  iunfold diskInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc1 Hb with Hb
  iunfold diskBody at Hb
  icases Hb with ⟨%I0, %stg0, %w0, %s0, Hds, Hrec0, Hb⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  icases Hb with (⟨Hl, Hs, %Hok, Hwin⟩ | ⟨Hc, -⟩)
  · simp only [diskWinRes]
    icases Hwin with ⟨%Hf, Hw⟩
    obtain ⟨hok', hab, hcur, halt⟩ := Hf
    have halt' : s0.alt = none := by
      rcases halt with h | ⟨h, _⟩; exact h; cases h
    obtain ⟨hL, hS⟩ := of_stab o I I' stg hab
    imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤ \ ↑diskN) (E2 := ⊤ \ ↑storeN)
      diff_storeN_sub_diskN) with Hmask
    iunfold winOf at Hw
    imod HAU $$ Hw Hnc with ⟨Hnc, HAU⟩
    imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%S, Hown, HRS⟩
    iunfold diskOwnS at Hown
    ihave %HS := ghostVar_agree _ _ _ _ _ $$ Hown Hs
    subst HS
    imod ghostVar_update_halves I'.absS g.γs _ _ $$ Hown Hs with ⟨Hown, Hs⟩
    imod ghostVar_update_halves ((I', stg, DiskWin.idle) : DiskRec) g.γw _ _ $$ Hrec Hrec0 with ⟨Hrec, Hrec0⟩
    imod HR $$ HRS [Hown] with HQ
    · iunfold diskOwnS; rw [← hS]; iexact Hown
    imod Hmask with -
    imod Hclose $$ [Hds Hrec0 Hl Hs] with -
    · inext; iunfold diskBody; iexists I', stg, DiskWin.idle, s0; iframe Hds Hrec0; ileft; iframe Hs
      rw [hL]; iframe Hl
      simp only [diskWinRes]
      ipureintro; exact ⟨hok', durSt_eta s0 _ hcur halt'⟩
    imodintro; iframe; ipureintro; exact hok'
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

end lemmas

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
