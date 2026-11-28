/-
(hraft_robust R3) The disk invariant's steps that commit a client's atomic update without a file write: a read
(`diskReadL`, `diskReadS`: the client's view agrees with the invariant's half, at the image the lock holds) and
`StageCommitIndex` (`diskStage`: both halves and the record move to the new staged index).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Inv

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode github_com.hashicorp.raft proto EtcdGrove

theorem diff_storeN_sub_diskN : (⊤ : CoPset) \ ↑storeN ⊆ ⊤ \ ↑diskN := by
  intro x hx
  rw [Std.LawfulSet.mem_diff] at hx ⊢
  exact ⟨hx.1, fun h => hx.2 (diskN_sub_storeN x h)⟩

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **A log read's commit** (see the file header). -/
theorem diskReadL (g : DiskGen) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (I : DiskImg) (stg : w64) (Q : LogAbs → IProp GF) :
    ⊢ diskInv g Wl Ws Wf -∗ ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.idle) : DiskRec) -∗ £ 1 -∗ £ 1 -∗
      (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, diskOwnL g A ∗ (diskOwnL g A ={∅,⊤ \ ↑storeN}=∗ Q A)) -∗
      |NC={⊤}=> ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.idle) : DiskRec) ∗ Q (I.absL stg) := by
  iintro #Hinv Hrec Hlc1 Hlc2 HAU Hnc
  iunfold diskInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc1 Hb with Hb
  iunfold diskBody at Hb
  icases Hb with ⟨%I0, %stg0, %w0, %s0, Hds, Hrec0, Hb⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  icases Hb with (⟨Hl, Hs, %Hok, Hw⟩ | ⟨Hc, -⟩)
  · imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤ \ ↑diskN) (E2 := ⊤ \ ↑storeN)
      diff_storeN_sub_diskN) with Hmask
    imod HAU $$ Hnc with ⟨Hnc, HAU⟩
    imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%A, Hown, Hcl⟩
    iunfold diskOwnL at Hown
    ihave %HA := ghostVar_agree _ _ _ _ _ $$ Hown Hl
    subst HA
    imod Hcl $$ [Hown] with HQ
    · iunfold diskOwnL; iexact Hown
    imod Hmask with -
    imod Hclose $$ [Hds Hrec0 Hl Hs Hw] with -
    · inext; iunfold diskBody; iexists I, stg, DiskWin.idle, s0; iframe Hds Hrec0; ileft; iframe
      ipureintro; exact Hok
    imodintro; iframe
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

/-- **A stable read's commit.** -/
theorem diskReadS (g : DiskGen) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (I : DiskImg) (stg : w64) (Q : StableAbs → IProp GF) :
    ⊢ diskInv g Wl Ws Wf -∗ ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.idle) : DiskRec) -∗ £ 1 -∗ £ 1 -∗
      (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ S, diskOwnS g S ∗ (diskOwnS g S ={∅,⊤ \ ↑storeN}=∗ Q S)) -∗
      |NC={⊤}=> ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.idle) : DiskRec) ∗ Q I.absS := by
  iintro #Hinv Hrec Hlc1 Hlc2 HAU Hnc
  iunfold diskInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc1 Hb with Hb
  iunfold diskBody at Hb
  icases Hb with ⟨%I0, %stg0, %w0, %s0, Hds, Hrec0, Hb⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  icases Hb with (⟨Hl, Hs, %Hok, Hw⟩ | ⟨Hc, -⟩)
  · imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤ \ ↑diskN) (E2 := ⊤ \ ↑storeN)
      diff_storeN_sub_diskN) with Hmask
    imod HAU $$ Hnc with ⟨Hnc, HAU⟩
    imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%S, Hown, Hcl⟩
    iunfold diskOwnS at Hown
    ihave %HS := ghostVar_agree _ _ _ _ _ $$ Hown Hs
    subst HS
    imod Hcl $$ [Hown] with HQ
    · iunfold diskOwnS; iexact Hown
    imod Hmask with -
    imod Hclose $$ [Hds Hrec0 Hl Hs Hw] with -
    · inext; iunfold diskBody; iexists I, stg, DiskWin.idle, s0; iframe Hds Hrec0; ileft; iframe
      ipureintro; exact Hok
    imodintro; iframe
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

/-- **`StageCommitIndex`'s commit**: the staged index moves to `idx`. -/
theorem diskStage (g : DiskGen) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (I : DiskImg) (stg idx : w64) (Q : IProp GF) :
    ⊢ diskInv g Wl Ws Wf -∗ ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.idle) : DiskRec) -∗ £ 1 -∗ £ 1 -∗
      (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, diskOwnL g A ∗ (diskOwnL g { A with staged := idx } ={∅,⊤ \ ↑storeN}=∗ Q)) -∗
      |NC={⊤}=> ghostVar g.γw (1 : Qp).half ((I, idx, DiskWin.idle) : DiskRec) ∗ Q := by
  iintro #Hinv Hrec Hlc1 Hlc2 HAU Hnc
  iunfold diskInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc1 Hb with Hb
  iunfold diskBody at Hb
  icases Hb with ⟨%I0, %stg0, %w0, %s0, Hds, Hrec0, Hb⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  icases Hb with (⟨Hl, Hs, %Hok, Hw⟩ | ⟨Hc, -⟩)
  · imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤ \ ↑diskN) (E2 := ⊤ \ ↑storeN)
      diff_storeN_sub_diskN) with Hmask
    imod HAU $$ Hnc with ⟨Hnc, HAU⟩
    imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%A, Hown, Hcl⟩
    iunfold diskOwnL at Hown
    ihave %HA := ghostVar_agree _ _ _ _ _ $$ Hown Hl
    subst HA
    rw [show ({ I.absL stg with staged := idx } : LogAbs) = I.absL idx from rfl]
    imod ghostVar_update_halves (I.absL idx) g.γl _ _ $$ Hown Hl with ⟨Hown, Hl⟩
    imod ghostVar_update_halves ((I, idx, DiskWin.idle) : DiskRec) g.γw _ _ $$ Hrec Hrec0 with ⟨Hrec, Hrec0⟩
    imod Hcl $$ [Hown] with HQ
    · iunfold diskOwnL; iexact Hown
    imod Hmask with -
    imod Hclose $$ [Hds Hrec0 Hl Hs Hw] with -
    · inext; iunfold diskBody; iexists I, idx, DiskWin.idle, s0; iframe Hds Hrec0; ileft; iframe Hl Hs
      isplitl []
      · ipureintro; exact Hok
      simp only [diskWinRes]
      iexact Hw
    imodintro; iframe
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

/-! ### raft's error variables (as `core/Laws.lean`'s, which the disk does not import) -/

theorem dk_errVals_elem (f : RaftErr → GoInterface) (c : RaftErr) :
    errVals (GF := GF) f ⊢ globalAddr c.var ↦□ f c ∗ errors.newVar c.var c.msg := by
  unfold errVals
  iintro ⟨-, #H⟩
  have hm : c ∈ RaftErr.all := by cases c <;> simp [RaftErr.all]
  iapply (BigSepL.bigSepL_mem hm) $$ H

theorem dk_pkgGlobals_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ⊢ pkgGlobals (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.hashicorp.raft

theorem dk_isRaftErr_of_init (c : RaftErr) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ⊢ ∃ e, isRaftErr c e := by
  iintro #H
  ihave Hg := dk_pkgGlobals_of_init $$ H
  unfold pkgGlobals
  icases Hg with ⟨⟨%f, #Hf⟩, -⟩
  iexists f c
  unfold isRaftErr
  iexists f; iframe #; ipureintro; rfl

theorem dk_isRaftErr_nonnil (c : RaftErr) (e : GoInterface) :
    isRaftErr (GF := GF) c e ⊢ ⌜e ≠ interface.nil⌝ := by
  unfold isRaftErr
  iintro ⟨%f, #H, %h⟩
  icases dk_errVals_elem f c $$ H with ⟨#P, #Hn⟩
  unfold errors.newVar
  icases Hn with ⟨%x, #Px, -⟩
  icombine P Px gives %h'
  ipureintro; subst h; rw [h']
  simp [interface.mkOk]

theorem dk_isRaftErr_global (c : RaftErr) (e : GoInterface) :
    isRaftErr (GF := GF) c e ⊢ globalAddr c.var ↦□ e := by
  unfold isRaftErr
  iintro ⟨%f, #H, %h⟩
  icases dk_errVals_elem f c $$ H with ⟨#P, -⟩
  subst h; iexact P

end lemmas

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
