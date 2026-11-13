/-
The shared mode of the tree: a step of a shared directory fd's read (`DirReadNext`), with a claim
on names of its directory (`wp_osDirReadNextS`) or blind (`wp_osDirReadNextBlind`), over one generic
step (`wp_dirReadS`). `TreeShared.lean` states the specs and takes their proofs from here. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedOpenDir

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **A step of a shared directory fd's read**, from what the caller's resources `F` say of the
state (`Q`, through the claims' authority): each outcome's new phase (`phName b`, `.done`, `phErr`;
`n` the log's length) keeps `PhOkS`, and gives the caller `WName`/`WDone`. -/
theorem wp_dirReadS (R : Roots) (fd : w64) (j : Ino) (ph : DirPhS) (F : IProp GF)
    (Q : OsState → Prop) (phName : Nat → GoString → DirPhS) (phErr : Nat → DirPhS)
    (WName : Nat → GoString → Prop) (WDone : Prop)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜Q st⌝)
    (hname : ∀ st (df : OsDirFd) u s r b, FsTreeWf st → df.ino = j → PhOkS st j ph df.rd → Q st →
      df.rd.cur st j = some (u, s, r) → s b = true → r b = false →
      PhOkS st j (phName st.fs.metaLog.length b) (.reading u s (fun x => r x || decide (x = b))) ∧
        WName st.fs.metaLog.length b)
    (hdone : ∀ st (df : OsDirFd) u s r, FsTreeWf st → df.ino = j → PhOkS st j ph df.rd → Q st →
      df.rd.cur st j = some (u, s, r) → (∀ b, u b = true → present st j b = true → r b = true) →
      WDone)
    (herr : ∀ st (df : OsDirFd) u s r, FsTreeWf st → df.ino = j → PhOkS st j ph df.rd → Q st →
      df.rd.cur st j = some (u, s, r) → PhOkS st j (phErr st.fs.metaLog.length) (.reading u s r))
    (hnd : ph ≠ .done)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osDirFdS (L := L) fd j ph -∗ F -∗
      (∀ v, F -∗ (∃ n, (∃ b, ⌜v = rdName b ∧ WName n b⌝ ∗ osDirFdS (L := L) fd j (phName n b)) ∨
          (⌜v = rdEnd ∧ WDone⌝ ∗ osDirFdS (L := L) fd j .done) ∨
          (∃ e : w64, ⌜e ≠ 0 ∧ v = rdErr e⌝ ∗ osDirFdS (L := L) fd j (phErr n))) -∗ Φ v) -∗
      WP (ExternalOp fsExt.name "DirReadNext" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hfd HF HΦ
  iapply wp_fs_stepM "DirReadNext" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  icases Hm with (Hm | Hm)
  · iexfalso; iapply legacy_dirFdS_excl st fd j ph $$ Hfd Hm
  unfold treeShared
  icases Hm with ⟨%V0, %s0, %Γdf, %Γc, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr⟩
  obtain ⟨hw, hc⟩ := hns
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  icases hF st Γn hR hcoh.2 $$ HAn HF with %hQ
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold osDirFdS
  icases gAuth_lookup _ _ _ _ _ _ $$ Hadfs Hfd with %Hfl
  obtain ⟨df, hdf, hino⟩ := dfdS_lookup hc Hfl
  have hph : PhOkS st j ph df.rd := by have := hc.ph fd _ df Hfl hdf; exact this
  have hnf : st.proc.fds !! fd = none := by
    cases hf : st.proc.fds !! fd with
    | none => rfl
    | some x => exact absurd hdf (by rw [hw.disj fd (by rw [hf]; simp)]; simp)
  have hin : df.ino ∈ st.tree := hw.dfds fd df hdf
  have hcur : ∃ u s r, df.rd.cur st j = some (u, s, r) := by
    cases hr : df.rd with
    | idle => exact ⟨_, _, _, rfl⟩
    | reading u s r => exact ⟨u, s, r, rfl⟩
    | done =>
      rw [hr] at hph
      cases ph with
      | done => exact absurd rfl hnd
      | _ => simp [PhOkS] at hph
  obtain ⟨u, s1, r, hcur⟩ := hcur
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hs : FilesSame st (setDfd st fd { df with rd := .reading u s1 r }) := filesSame_setDfd _ _ _
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 hs Hag
    refine ⟨_, h, _, ⟨fd, df, u, s1, r, rfl, hdf, by rw [hino]; exact hcur,
      .inr (.inr ⟨1, by decide, rfl, rfl⟩)⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', df', u', s', r', hv, hdf', hcur', hres⟩ := Hst
  cases go.intoVal_inj hv
  rw [hdf] at hdf'; cases hdf'
  rw [hino, hcur] at hcur'; cases hcur'
  have hfin : ∀ (rd' : OsDirRead) (ph' : DirPhS), PhOkS st j ph' rd' →
      st' = setDfd st fd { df with rd := rd' } →
      ⊢ osWorld (L := L) st Γb Γm Γf Γt h -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdfS Γdf -∗
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdfS fd (DFrac.own 1) (j, ph) ==∗
        osWorld (L := L) st' Γb Γm Γf Γt h' ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdfS (<[fd := (j, ph')]> Γdf) ∗
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdfS fd (DFrac.own 1) (j, ph') ∗
        ⌜FsTreeWf st' ∧ TreeCohS st' s0 (<[fd := (j, ph')]> Γdf) Γc ∧ CommitGrows st st' ∧
          st'.fs.roots = st.fs.roots ∧ st'.fs.treeDur = st.fs.treeDur ∧
          st'.fs.metaLog = st.fs.metaLog⌝ := by
    intro rd' ph' hok hst
    subst hst
    have hw' := fsTreeWf_setDfd hw (df' := { df with rd := rd' }) hnf hin
    have hc' := treeCohS_setDfd (fd := fd) (df' := { df with rd := rd' }) (x := (j, ph')) hc
      hino.symm (hok.congr rfl rfl)
    iintro Hw HAdf Hfd
    imod gAuth_update _ _ _ _ _ (j, ph') $$ HAdf Hfd with ⟨HAdf, Hfd⟩
    imod osWorld_filesSame (st := st) (st' := setDfd st fd { df with rd := rd' })
      (filesSame_setDfd _ _ _) Hr Hfr $$ Hw with Hw
    imodintro
    iframe
    ipureintro
    exact ⟨hw', hc', commitGrows_of_eq rfl, rfl, rfl, rfl⟩
  ihave Hw : osWorld (L := L) st Γb Γm Γf Γt h $$ [HAb HAm HAf HAt Htok Hcells Hσ]
  · unfold osWorld; iframe; ipureintro; exact Hwc
  rcases hres with ⟨b, hsb, hrb, hst, rfl⟩ | ⟨hall, hst, rfl⟩ | ⟨e, he, hst, rfl⟩
  · obtain ⟨hok, hW⟩ := hname st df u s1 r b hw hino hph hQ hcur hsb hrb
    imod hfin _ _ hok hst $$ Hw Hadfs Hfd with ⟨Hw, Hadfs, Hfd, %hp⟩
    obtain ⟨hw', hc', hcg, hro, hdu, hlo⟩ := hp
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) hcg $$ Hcm
      iright
      try unfold treeShared
      iexists V0, s0, <[fd := (j, phName st.fs.metaLog.length b)]> Γdf, Γc
      rw [hro, hdu, hlo]
      iframe
      ipureintro; exact ⟨hw', hc'⟩
    iapply wp_value'
    iapply HΦ $$ %(rdName b) HF
    iexists st.fs.metaLog.length
    ileft; iexists b; iframe Hfd; ipureintro; exact ⟨rfl, hW⟩
  · have hW := hdone st df u s1 r hw hino hph hQ hcur (by rw [← hino]; exact hall)
    imod hfin .done .done (by simp [PhOkS]) hst $$ Hw Hadfs Hfd with ⟨Hw, Hadfs, Hfd, %hp⟩
    obtain ⟨hw', hc', hcg, hro, hdu, hlo⟩ := hp
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) hcg $$ Hcm
      iright
      try unfold treeShared
      iexists V0, s0, <[fd := (j, .done)]> Γdf, Γc
      rw [hro, hdu, hlo]
      iframe
      ipureintro; exact ⟨hw', hc'⟩
    iapply wp_value'
    iapply HΦ $$ %(rdEnd) HF
    iexists st.fs.metaLog.length
    iright; ileft; iframe Hfd; ipureintro; exact ⟨rfl, hW⟩
  · have hok := herr st df u s1 r hw hino hph hQ hcur
    imod hfin _ _ hok hst $$ Hw Hadfs Hfd with ⟨Hw, Hadfs, Hfd, %hp⟩
    obtain ⟨hw', hc', hcg, hro, hdu, hlo⟩ := hp
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) hcg $$ Hcm
      iright
      try unfold treeShared
      iexists V0, s0, <[fd := (j, phErr st.fs.metaLog.length)]> Γdf, Γc
      rw [hro, hdu, hlo]
      iframe
      ipureintro; exact ⟨hw', hc'⟩
    iapply wp_value'
    iapply HΦ $$ %(rdErr e) HF
    iexists st.fs.metaLog.length
    iright; iright; iexists e; iframe Hfd; ipureintro; exact ⟨he, rfl⟩

end specs

/-- The names a read has seen are valid, while it is not done. -/
theorem phOkS_seen {st : OsState} {j : Ino} {ph : DirPhS} {rd : OsDirRead} {u s r : GoString → Bool}
    (hph : PhOkS st j ph rd) (hnd : ph ≠ .done) (hcur : rd.cur st j = some (u, s, r)) :
    ∀ b, s b = true → NameOk b := by
  intro b hb
  cases ph with
  | done => exact absurd rfl hnd
  | idle =>
    cases rd with
    | idle =>
      simp only [OsDirRead.cur, Option.some.injEq, Prod.mk.injEq] at hcur
      obtain ⟨-, rfl, -⟩ := hcur
      simp only [present, Bool.and_eq_true, decide_eq_true_eq] at hb; exact hb.1
    | _ => simp [PhOkS] at hph
  | reading N r0 rs =>
    cases rd with
    | reading u' s' r' =>
      simp only [OsDirRead.cur, Option.some.injEq, Prod.mk.injEq] at hcur
      obtain ⟨-, rfl, -⟩ := hcur
      exact hph.2.1 b hb
    | _ => simp [PhOkS] at hph

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem wp_osDirReadNextBlind' (R : Roots) (fd : w64) (j : Ino) (ph : DirPhS) (hph : ph ≠ .done)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osDirFdS (L := L) fd j ph -∗
      (∀ v, ((∃ b, ⌜v = rdName b ∧ NameOk b⌝ ∗ osDirFdS (L := L) fd j (.reading (.only []) 0 [])) ∨
          (⌜v = rdEnd⌝ ∗ osDirFdS (L := L) fd j .done) ∨
          (∃ e : w64, ⌜e ≠ 0 ∧ v = rdErr e⌝ ∗ osDirFdS (L := L) fd j (.reading (.only []) 0 []))) -∗
        Φ v) -∗
      WP (ExternalOp fsExt.name "DirReadNext" (Val (#fd))) @ s; E {{ Φ }} := by
  have hok : ∀ st (u s r : GoString → Bool), (∀ b, s b = true → NameOk b) →
      PhOkS st j (.reading (.only []) 0 []) (.reading u s r) := by
    intro st u s r hs
    exact ⟨Nat.zero_le _, hs, fun _ b hb => by simp [NameSet.Mem] at hb⟩
  iintro #Hinv #Hsi Hfd HΦ
  iapply wp_dirReadS R fd j ph emp (fun _ => True) (fun _ _ => .reading (.only []) 0 [])
    (fun _ => .reading (.only []) 0 []) (fun _ b => NameOk b) True
    (fun _ _ _ _ => by iintro _ _; ipureintro; trivial)
    (fun st df u s r b _ _ hph' _ hcur hsb _ =>
      ⟨hok st _ _ _ (phOkS_seen hph' hph hcur), phOkS_seen hph' hph hcur b hsb⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun st df u s r _ _ hph' _ hcur => hok st _ _ _ (phOkS_seen hph' hph hcur))
    hph hE hE' Φ $$ Hinv Hsi Hfd []
  · iempintro
  iintro %v - ⟨%n, Hv⟩
  iapply HΦ
  icases Hv with (⟨%b, ⟨%hv, %hb⟩, Hfd⟩ | ⟨⟨%hv, -⟩, Hfd⟩ | ⟨%e, %he, Hfd⟩)
  · ileft; iexists b; iframe Hfd; ipureintro; exact ⟨hv, hb⟩
  · iright; ileft; iframe Hfd; ipureintro; exact hv
  · iright; iright; iexists e; iframe Hfd; ipureintro; exact he

end specs

end Fs
end Perennial

end
