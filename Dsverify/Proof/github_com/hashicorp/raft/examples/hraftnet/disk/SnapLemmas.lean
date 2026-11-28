/-
(hraft_robust R3) The snapshot store's invariant's steps (`SnapInv.lean`), as the disk's (`InvLemmas`,
`WriteLemmas`, `BootLemmas`):

* `snapRead`: a read's commit (`List`, `Open`): the client's view agrees with the invariant's half;
* `snapCommitKeep`: a `Close` that keeps the older latest commits at once (no file write), the close obligation
  given to the client's update;
* `snapWriteAU`: a persisting `Close`'s `durable.Write` updates: at the rename the window opens and the close
  obligation moves into the invariant, at the sync `alt := none`;
* `snapCommit`: after `Write` returned, the close obligation comes out, the client's update runs with it, the
  view becomes the new latest and the window closes idle;
* `snap_boot`, `snap_boot_fresh`, `freshSnapWriteAU`: a generation's start (from the file's image, or
  `FreshSnaps`'s, with the caller's `Wf` until its write is synced).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.SnapInv
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.WriteLemmas

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode Iris.Std github_com.hashicorp.raft proto EtcdGrove

/-- A well-formed image from its encoding's length (a Go slice's). -/
theorem snapOk_of_enc (S : SnapImg) (hl : (encSnap S).length < 2 ^ 63) : S.Ok := by
  unfold SnapImg.Ok
  unfold encSnap at hl
  rcases h : S.latest with _ | ⟨m, b⟩
  · trivial
  · simp only [h, encCfg, encBytes, List.length_append, encU64_length] at hl
    have hS : ∀ s, 1 ≤ (encServer s).length := fun s => by
      simp [encServer, encBytes, encU64_length]
      omega
    have := len_le_flatMap m.servers encServer hS
    refine ⟨by omega, by omega, by omega, fun s hs => ?_⟩
    have := mem_le_flatMap m.servers encServer s hs
    simp only [encServer, encBytes, List.length_append, encU64_length] at this
    omega

/-- The empty image (what `FreshSnaps` writes: `nextID` zero, no snapshot). -/
def emptySnap : SnapImg := ⟨W64 0, none⟩

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **A read's commit** (see the file header). -/
theorem snapRead (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF)
    (lat : SnapLatest) (lt : SLat) (Q : SnapLatest → IProp GF) :
    ⊢ snapsInv g Qc Wf -∗ ghostVar g.γw (1 : Qp).half ((lat, lt, SnapWin.idle) : SnapRec) -∗ £ 1 -∗ £ 1 -∗
      (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, snapsOwn g old ∗ (snapsOwn g old ={∅,⊤ \ ↑storeN}=∗ Q old)) -∗
      |NC={⊤}=> ghostVar g.γw (1 : Qp).half ((lat, lt, SnapWin.idle) : SnapRec) ∗ Q lat := by
  iintro #Hinv Hrec Hlc1 Hlc2 HAU Hnc
  iunfold snapsInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc1 Hb with Hb
  iunfold snapsBody at Hb
  icases Hb with ⟨%lat0, %lt0, %w0, %s0, Hds, Hrec0, Hb⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  icases Hb with (⟨Hl, #Hr, %Hok, Hw⟩ | ⟨Hc, -⟩)
  · imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤ \ ↑snapsN) (E2 := ⊤ \ ↑storeN)
      diff_storeN_sub_snapsN) with Hmask
    imod HAU $$ Hnc with ⟨Hnc, HAU⟩
    imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%A, Hown, Hcl⟩
    iunfold snapsOwn at Hown
    ihave %HA := ghostVar_agree _ _ _ _ _ $$ Hown Hl
    subst HA
    imod Hcl $$ [Hown] with HQ
    · iunfold snapsOwn; iexact Hown
    imod Hmask with -
    imod Hclose $$ [Hds Hrec0 Hl Hw] with -
    · inext; iunfold snapsBody; iexists A, lt, SnapWin.idle, s0; iframe Hds Hrec0; ileft; iframe Hl Hw
      iframe #; ipureintro; exact Hok
    imodintro; iframe
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

/-- **A `Close` that keeps the older latest** commits at once (see the file header). -/
theorem snapCommitKeep (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF)
    (lat : SnapLatest) (lt : SLat) (m : SnapshotMeta) (b : List w8) (R : IProp GF)
    (h : newerSnap lat m b = lat) :
    ⊢ snapsInv g Qc Wf -∗ ghostVar g.γw (1 : Qp).half ((lat, lt, SnapWin.idle) : SnapRec) -∗ £ 1 -∗ £ 1 -∗
      Qc m b -∗
      (Qc m b -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, snapsOwn g old ∗
        (snapsOwn g (newerSnap old m b) ={∅,⊤ \ ↑storeN}=∗ R)) -∗
      |NC={⊤}=> ghostVar g.γw (1 : Qp).half ((lat, lt, SnapWin.idle) : SnapRec) ∗ R := by
  iintro #Hinv Hrec Hlc1 Hlc2 HQc HAU Hnc
  iunfold snapsInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc1 Hb with Hb
  iunfold snapsBody at Hb
  icases Hb with ⟨%lat0, %lt0, %w0, %s0, Hds, Hrec0, Hb⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  icases Hb with (⟨Hl, #Hr, %Hok, Hw⟩ | ⟨Hc, -⟩)
  · imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤ \ ↑snapsN) (E2 := ⊤ \ ↑storeN)
      diff_storeN_sub_snapsN) with Hmask
    imod HAU $$ HQc Hnc with ⟨Hnc, HAU⟩
    imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%A, Hown, Hcl⟩
    iunfold snapsOwn at Hown
    ihave %HA := ghostVar_agree _ _ _ _ _ $$ Hown Hl
    subst HA
    imod Hcl $$ [Hown] with HQ
    · iunfold snapsOwn; rw [h]; iexact Hown
    imod Hmask with -
    imod Hclose $$ [Hds Hrec0 Hl Hw] with -
    · inext; iunfold snapsBody; iexists A, lt, SnapWin.idle, s0; iframe Hds Hrec0; ileft; iframe Hl Hw
      iframe #; ipureintro; exact Hok
    imodintro; iframe
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

/-- **A persisting `Close`'s `durable.Write` updates** (see the file header). -/
theorem snapWriteAU (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF)
    (lat : SnapLatest) (lt : SLat) (m : SnapshotMeta) (b : List w8) (sm : SMeta) (nid : w64) (P : IProp GF)
    (hnew : newerSnap lat m b = some (m, b)) (hb : b.length < 2 ^ 63) :
    ⊢ snapsInv g Qc Wf -∗ ghostVar g.γw (1 : Qp).half ((lat, lt, SnapWin.idle) : SnapRec) -∗
      metaRep m sm b.length -∗ Qc m b -∗
      (ghostVar g.γw (1 : Qp).half ((lat, lt, SnapWin.open m b sm nid true) : SnapRec) -∗ P) -∗
      (⌜(encSnap ⟨nid, some (sm, b)⟩).length < 2 ^ 63⌝ -∗
        AU <{ ∃∃ s : DurFs.DurSt, DurFs.durSt (GF := GF) g.γd s }> @ DurFs.durAuMask, ∅
          <{ DurFs.durSt (GF := GF) g.γd ⟨some (encSnap ⟨nid, some (sm, b)⟩), some s.cur⟩, COMM
            DurFs.durWriteSync (GF := GF) g.γd P }>) := by
  iintro #Hinv Hrec #Hmr HQc HK %hlen
  have hok' : ltOk (some (sm, b)) := snapOk_of_enc _ hlen
  iauintro
  unfold atomic_acc
  iunfold snapsInv at Hinv
  imod inv_acc (E := DurFs.durAuMask) snapsN_sub_durAu $$ Hinv with ⟨Hi, Hclose⟩
  iunfold snapsBody at Hi
  imod later_exists_except0 $$ Hi with ⟨%lat0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%lt0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%w0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%s0, Hi⟩
  icases Hi with ⟨Hds, Hrec0, Hb⟩
  imod Hds
  imod Hrec0
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑snapsN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists s0
  iframe Hds
  isplit
  · -- abort
    iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hrec0 Hb] with -
    · inext; iunfold snapsBody; iexists lat, lt, SnapWin.idle, s0; iframe
    imodintro
    iframe
  -- the rename
  iintro Hds
  imod Hclose2 with -
  imod ghostVar_update_halves ((lat, lt, SnapWin.open m b sm nid false) : SnapRec) g.γw _ _ $$ Hrec Hrec0
    with ⟨Hrec, Hrec0⟩
  ihave Hb' : iprop(▷ ((ghostVar g.γl (1 : Qp).half lat ∗ latRep lat lt ∗ ⌜ltOk lt⌝ ∗
      snapWinRes Qc Wf lat lt ⟨some (encSnap ⟨nid, some (sm, b)⟩), some s0.cur⟩
        (SnapWin.open m b sm nid false)) ∨
      crashed ∗ token g.γk)) $$ [Hb HQc]
  · icases later_or.1 $$ Hb with (Hb | Hb)
    · inext
      ileft
      icases Hb with ⟨Hl, #Hr, %Hok, Hidle⟩
      simp only [snapWinRes]
      icases Hidle with %Hidle
      obtain ⟨nid0, hs0⟩ := Hidle
      iframe Hl HQc
      iframe #
      ipureintro
      subst hs0
      exact ⟨Hok, hnew, hb, hok', trivial, Or.inr ⟨trivial, nid0, rfl⟩⟩
    · inext; iright; iexact Hb
  imod Hclose $$ [Hds Hrec0 Hb'] with -
  · inext; iunfold snapsBody
    iexists lat, lt, SnapWin.open m b sm nid false, ⟨some (encSnap ⟨nid, some (sm, b)⟩), some s0.cur⟩
    iframe
  imodintro
  -- the directory's sync
  iintro Hnc
  iauintro
  unfold atomic_acc
  imod inv_acc (E := DurFs.durAuMask) snapsN_sub_durAu $$ Hinv with ⟨Hi, Hclose⟩
  iunfold snapsBody at Hi
  imod later_exists_except0 $$ Hi with ⟨%lat1, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%lt1, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%w1, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%s1, Hi⟩
  icases Hi with ⟨Hds, Hrec0, Hb⟩
  imod Hds
  imod Hrec0
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑snapsN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists s1
  iframe Hds
  isplit
  · iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hrec0 Hb] with -
    · inext; iunfold snapsBody; iexists lat, lt, SnapWin.open m b sm nid false, s1; iframe
    imodintro
    iframe
  iintro Hds
  imod Hclose2 with -
  imod ghostVar_update_halves ((lat, lt, SnapWin.open m b sm nid true) : SnapRec) g.γw _ _ $$ Hrec Hrec0
    with ⟨Hrec, Hrec0⟩
  ihave Hb' : iprop(▷ ((ghostVar g.γl (1 : Qp).half lat ∗ latRep lat lt ∗ ⌜ltOk lt⌝ ∗
      snapWinRes Qc Wf lat lt ⟨s1.cur, none⟩ (SnapWin.open m b sm nid true)) ∨
      crashed ∗ token g.γk)) $$ [Hb]
  · icases later_or.1 $$ Hb with (Hb | Hb)
    · inext
      ileft
      icases Hb with ⟨Hl, #Hr, %Hok, Hwin⟩
      simp only [snapWinRes]
      icases Hwin with ⟨%Hf, #Hmr', HQc⟩
      iframe Hl HQc
      iframe #
      ipureintro
      exact ⟨Hok, Hf.1, Hf.2.1, Hf.2.2.1, Hf.2.2.2.1, Or.inl trivial⟩
    · inext; iright; iexact Hb
  imod Hclose $$ [Hds Hrec0 Hb'] with -
  · inext; iunfold snapsBody; iexists lat, lt, SnapWin.open m b sm nid true, ⟨s1.cur, none⟩
    iframe
  imodintro
  iframe Hnc
  iapply HK $$ Hrec

/-- **A persisting `Close`'s commit**, after `Write` returned (see the file header). -/
theorem snapCommit (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF)
    (lat : SnapLatest) (lt : SLat) (m : SnapshotMeta) (b : List w8) (sm : SMeta) (nid : w64) (R : IProp GF) :
    ⊢ snapsInv g Qc Wf -∗ ghostVar g.γw (1 : Qp).half ((lat, lt, SnapWin.open m b sm nid true) : SnapRec) -∗
      £ 1 -∗ £ 1 -∗
      (Qc m b -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, snapsOwn g old ∗
        (snapsOwn g (newerSnap old m b) ={∅,⊤ \ ↑storeN}=∗ R)) -∗
      |NC={⊤}=> ghostVar g.γw (1 : Qp).half ((some (m, b), some (sm, b), SnapWin.idle) : SnapRec) ∗ R := by
  iintro #Hinv Hrec Hlc1 Hlc2 HAU Hnc
  iunfold snapsInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc1 Hb with Hb
  iunfold snapsBody at Hb
  icases Hb with ⟨%lat0, %lt0, %w0, %s0, Hds, Hrec0, Hb⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  icases Hb with (⟨Hl, #Hr, %Hok, Hwin⟩ | ⟨Hc, -⟩)
  · simp only [snapWinRes]
    icases Hwin with ⟨%Hf, #Hmr, HQc⟩
    obtain ⟨hnew, hb, hok', hcur, halt⟩ := Hf
    have halt' : s0.alt = none := by
      rcases halt with h | ⟨h, _⟩; exact h; cases h
    imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤ \ ↑snapsN) (E2 := ⊤ \ ↑storeN)
      diff_storeN_sub_snapsN) with Hmask
    imod HAU $$ HQc Hnc with ⟨Hnc, HAU⟩
    imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%A, Hown, HRA⟩
    iunfold snapsOwn at Hown
    ihave %HA := ghostVar_agree _ _ _ _ _ $$ Hown Hl
    subst HA
    imod ghostVar_update_halves (some (m, b) : SnapLatest) g.γl _ _ $$ Hown Hl with ⟨Hown, Hl⟩
    imod ghostVar_update_halves ((some (m, b), some (sm, b), SnapWin.idle) : SnapRec) g.γw _ _ $$ Hrec Hrec0
      with ⟨Hrec, Hrec0⟩
    imod HRA $$ [Hown] with HR
    · iunfold snapsOwn; rw [hnew]; iexact Hown
    imod Hmask with -
    imod Hclose $$ [Hds Hrec0 Hl] with -
    · inext; iunfold snapsBody; iexists some (m, b), some (sm, b), SnapWin.idle, s0
      iframe Hds Hrec0; ileft; iframe Hl
      simp only [latRep, snapWinRes]
      iframe #
      ipureintro
      refine ⟨hok', nid, ?_⟩
      rw [durSt_eta s0 _ hcur halt']
    imodintro; iframe
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

/-- **A generation's start from the file's image**. -/
theorem snap_boot (γd : DurFs.DurGS) (f : DurFs.DFile) (R : Fs.Roots) (Qc : SnapshotMeta → List w8 → IProp GF)
    (Wf : IProp GF) (S : SnapImg) (hok : S.Ok) (lat : SnapLatest) (E : CoPset) :
    ⊢ DurFs.durSt γd ⟨some (encSnap S), none⟩ -∗ latRep lat S.latest ={E}=∗ ∃ g : SnapGen,
      ⌜g.γd = γd ∧ g.f = f ∧ g.R = R⌝ ∗ snapsInv g Qc Wf ∗ token g.γk ∗ snapsOwn g lat ∗
      ghostVar g.γw (1 : Qp).half ((lat, S.latest, SnapWin.idle) : SnapRec) := by
  iintro Hds #Hr
  imod ghostVar_alloc (GF := GF) lat with ⟨%γl, Hl⟩
  imod ghostVar_alloc (GF := GF) ((lat, S.latest, SnapWin.idle) : SnapRec) with ⟨%γw, Hw⟩
  imod token_alloc (GF := GF) with ⟨%γk, Hk⟩
  icases ghostVar_halves γl _ $$ Hl with ⟨Hl1, Hl2⟩
  icases ghostVar_halves γw _ $$ Hw with ⟨Hw1, Hw2⟩
  imod inv_alloc snapsN E (snapsBody (⟨γd, f, R, γl, γw, γk⟩ : SnapGen) Qc Wf) $$ [Hds Hl1 Hw1] with #Hinv
  · inext; iunfold snapsBody; iexists lat, S.latest, SnapWin.idle, ⟨some (encSnap S), none⟩
    iframe; ileft; iframe; iframe #; simp only [snapWinRes]; ipureintro
    exact ⟨(ltOk_iff S.nextID S.latest).1 hok, S.nextID, rfl⟩
  imodintro
  iexists ⟨γd, f, R, γl, γw, γk⟩
  unfold snapsOwn snapsInv
  iframe; iframe #
  ipureintro; exact ⟨rfl, rfl, rfl⟩

/-- **`FreshSnaps`'s generation**, before it writes the empty image. -/
theorem snap_boot_fresh (γd : DurFs.DurGS) (f : DurFs.DFile) (R : Fs.Roots)
    (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (s : DurFs.DurSt) (E : CoPset) :
    ⊢ DurFs.durSt γd s -∗ Wf ={E}=∗ ∃ g : SnapGen,
      ⌜g.γd = γd ∧ g.f = f ∧ g.R = R⌝ ∗ snapsInv g Qc Wf ∗ token g.γk ∗ snapsOwn g none ∗
      ghostVar g.γw (1 : Qp).half ((none, none, SnapWin.fresh false) : SnapRec) := by
  iintro Hds HWf
  imod ghostVar_alloc (GF := GF) (none : SnapLatest) with ⟨%γl, Hl⟩
  imod ghostVar_alloc (GF := GF) ((none, none, SnapWin.fresh false) : SnapRec) with ⟨%γw, Hw⟩
  imod token_alloc (GF := GF) with ⟨%γk, Hk⟩
  icases ghostVar_halves γl _ $$ Hl with ⟨Hl1, Hl2⟩
  icases ghostVar_halves γw _ $$ Hw with ⟨Hw1, Hw2⟩
  imod inv_alloc snapsN E (snapsBody (⟨γd, f, R, γl, γw, γk⟩ : SnapGen) Qc Wf) $$ [Hds Hl1 Hw1 HWf] with #Hinv
  · inext; iunfold snapsBody; iexists none, none, SnapWin.fresh false, s
    iframe; ileft; iframe; simp only [latRep, snapWinRes]; iframe
    ipureintro; exact ⟨trivial, by intro h; cases h⟩
  imodintro
  iexists ⟨γd, f, R, γl, γw, γk⟩
  unfold snapsOwn snapsInv
  iframe; iframe #
  ipureintro; exact ⟨rfl, rfl, rfl⟩

/-- **`FreshSnaps`'s `durable.Write` updates**: the rename records that the file holds the empty image, the sync
closes the window idle and gives `Wf` back. -/
theorem freshSnapWriteAU (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (P : IProp GF) :
    ⊢ snapsInv g Qc Wf -∗ ghostVar g.γw (1 : Qp).half ((none, none, SnapWin.fresh false) : SnapRec) -∗
      £ 1 -∗ (ghostVar g.γw (1 : Qp).half ((none, none, SnapWin.idle) : SnapRec) -∗ Wf -∗ P) -∗
      (⌜(encSnap emptySnap).length < 2 ^ 63⌝ -∗
        AU <{ ∃∃ s : DurFs.DurSt, DurFs.durSt (GF := GF) g.γd s }> @ DurFs.durAuMask, ∅
          <{ DurFs.durSt (GF := GF) g.γd ⟨some (encSnap emptySnap), some s.cur⟩, COMM
            DurFs.durWriteSync (GF := GF) g.γd P }>) := by
  iintro #Hinv Hrec Hlc HK %_
  iauintro
  unfold atomic_acc
  iunfold snapsInv at Hinv
  imod inv_acc (E := DurFs.durAuMask) snapsN_sub_durAu $$ Hinv with ⟨Hi, Hclose⟩
  iunfold snapsBody at Hi
  imod later_exists_except0 $$ Hi with ⟨%lat0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%lt0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%w0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%s0, Hi⟩
  icases Hi with ⟨Hds, Hrec0, Hb⟩
  imod Hds
  imod Hrec0
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑snapsN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists s0
  iframe Hds
  isplit
  · iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hrec0 Hb] with -
    · inext; iunfold snapsBody; iexists none, none, SnapWin.fresh false, s0; iframe
    imodintro
    iframe
  iintro Hds
  imod Hclose2 with -
  imod ghostVar_update_halves ((none, none, SnapWin.fresh true) : SnapRec) g.γw _ _ $$ Hrec Hrec0
    with ⟨Hrec, Hrec0⟩
  ihave Hb' : iprop(▷ ((ghostVar g.γl (1 : Qp).half (none : SnapLatest) ∗ latRep (none : SnapLatest) none ∗
      ⌜ltOk none⌝ ∗ snapWinRes Qc Wf none none ⟨some (encSnap emptySnap), some s0.cur⟩ (SnapWin.fresh true)) ∨
      crashed ∗ token g.γk)) $$ [Hb]
  · icases later_or.1 $$ Hb with (Hb | Hb)
    · inext
      ileft
      icases Hb with ⟨Hl, #Hr, %Hok, Hwin⟩
      simp only [snapWinRes]
      icases Hwin with ⟨HWf, -⟩
      iframe; iframe #
      ipureintro; exact ⟨Hok, fun _ => ⟨W64 0, rfl⟩⟩
    · inext; iright; iexact Hb
  imod Hclose $$ [Hds Hrec0 Hb'] with -
  · inext; iunfold snapsBody; iexists none, none, SnapWin.fresh true, ⟨some (encSnap emptySnap), some s0.cur⟩
    iframe
  imodintro
  -- the sync: the window closes idle, `Wf` comes back
  iintro Hnc
  iauintro
  unfold atomic_acc
  imod inv_acc (E := DurFs.durAuMask) snapsN_sub_durAu $$ Hinv with ⟨Hi, Hclose⟩
  iunfold snapsBody at Hi
  imod later_exists_except0 $$ Hi with ⟨%lat1, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%lt1, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%w1, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%s1, Hi⟩
  icases Hi with ⟨Hds, Hrec0, Hb⟩
  imod Hds
  imod Hrec0
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hrec Hrec0
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  imod notCrashed_or_crashed $$ [$Hnc $Hb] with ⟨Hnc, Hb⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑snapsN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists s1
  iframe Hds
  isplit
  · iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hrec0 Hb] with -
    · inext; iunfold snapsBody; iexists none, none, SnapWin.fresh true, s1; iframe
    imodintro
    iframe
  iintro Hds
  imod Hclose2 with -
  imod lc_fupd_elim_later $$ Hlc Hb with Hb
  icases Hb with ⟨Hl, #Hr, %Hok, Hwin⟩
  simp only [snapWinRes]
  icases Hwin with ⟨HWf, %Hcur⟩
  obtain ⟨nid1, hcur⟩ := Hcur trivial
  imod ghostVar_update_halves ((none, none, SnapWin.idle) : SnapRec) g.γw _ _ $$ Hrec Hrec0
    with ⟨Hrec, Hrec0⟩
  imod Hclose $$ [Hds Hrec0 Hl] with -
  · inext; iunfold snapsBody; iexists none, none, SnapWin.idle, ⟨s1.cur, none⟩
    iframe; ileft; iframe; iframe #; simp only [snapWinRes]; ipureintro
    exact ⟨Hok, nid1, by rw [hcur]⟩
  imodintro
  iframe Hnc
  iapply HK $$ Hrec HWf

end lemmas

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
