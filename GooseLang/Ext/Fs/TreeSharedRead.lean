/-
The shared mode of the tree: a step of a shared directory fd's read (`DirReadNext`), with a claim
on names of its directory (`wp_osDirReadNextS`) or blind (`wp_osDirReadNextBlind`), over one generic
step (`wp_dirReadS`). `TreeShared.lean` states the specs and takes their proofs from here. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedOpenDir
public import GooseLang.Ext.Fs.TreeSharedLog
public import GooseLang.Ext.Fs.TreeSharedLaws

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
`n` the log's length, of which `WN n` holds) keeps `PhOkS`, and gives the caller `WName`/`WDone`. -/
theorem wp_dirReadS (R : Roots) (fd : w64) (j : Ino) (ph : DirPhS) (F : IProp GF)
    (Q : OsState → Prop) (phName : Nat → GoString → DirPhS) (phErr : Nat → DirPhS)
    (WName : Nat → GoString → Prop) (WDone : Prop) (WN : Nat → Prop)
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
    (hwn : ∀ st, FsTreeWf st → Q st → WN st.fs.metaLog.length)
    (hnd : ph ≠ .done)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osDirFdS (L := L) fd j ph -∗ F -∗
      (∀ v, F -∗ (∃ n, ⌜WN n⌝ ∗ ((∃ b, ⌜v = rdName b ∧ WName n b⌝ ∗ osDirFdS (L := L) fd j (phName n b)) ∨
          (⌜v = rdEnd ∧ WDone⌝ ∗ osDirFdS (L := L) fd j .done) ∨
          (∃ e : w64, ⌜e ≠ 0 ∧ v = rdErr e⌝ ∗ osDirFdS (L := L) fd j (phErr n)))) -∗ Φ v) -∗
      WP (ExternalOp fsExt.name "DirReadNext" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hfd HF HΦ
  iapply wp_fs_stepM "DirReadNext" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  icases Hm with (Hm | Hm)
  · iexfalso; iapply legacy_dirFdS_excl st fd j ph $$ Hfd Hm
  unfold treeShared
  icases Hm with ⟨%V0, %s0, %Γdf, %Γc, %Γg, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
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
        ⌜FsTreeWf st' ∧ TreeCohS st' s0 (<[fd := (j, ph')]> Γdf) Γc Γg ∧ CommitGrows st st' ∧
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
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) hcg $$ Hcm
      iright
      try unfold treeShared
      iexists V0, s0, <[fd := (j, phName st.fs.metaLog.length b)]> Γdf, Γc, Γg
      rw [hro, hdu, hlo]
      iframe
      ipureintro; exact ⟨hw', hc'⟩
    iapply wp_value'
    iapply HΦ $$ %(rdName b) HF
    iexists st.fs.metaLog.length
    isplitr
    · ipureintro; exact hwn st hw hQ
    ileft; iexists b; iframe Hfd; ipureintro; exact ⟨rfl, hW⟩
  · have hW := hdone st df u s1 r hw hino hph hQ hcur (by rw [← hino]; exact hall)
    imod hfin .done .done (by simp [PhOkS]) hst $$ Hw Hadfs Hfd with ⟨Hw, Hadfs, Hfd, %hp⟩
    obtain ⟨hw', hc', hcg, hro, hdu, hlo⟩ := hp
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) hcg $$ Hcm
      iright
      try unfold treeShared
      iexists V0, s0, <[fd := (j, .done)]> Γdf, Γc, Γg
      rw [hro, hdu, hlo]
      iframe
      ipureintro; exact ⟨hw', hc'⟩
    iapply wp_value'
    iapply HΦ $$ %(rdEnd) HF
    iexists st.fs.metaLog.length
    isplitr
    · ipureintro; exact hwn st hw hQ
    iright; ileft; iframe Hfd; ipureintro; exact ⟨rfl, hW⟩
  · have hok := herr st df u s1 r hw hino hph hQ hcur
    imod hfin _ _ hok hst $$ Hw Hadfs Hfd with ⟨Hw, Hadfs, Hfd, %hp⟩
    obtain ⟨hw', hc', hcg, hro, hdu, hlo⟩ := hp
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) hcg $$ Hcm
      iright
      try unfold treeShared
      iexists V0, s0, <[fd := (j, phErr st.fs.metaLog.length)]> Γdf, Γc, Γg
      rw [hro, hdu, hlo]
      iframe
      ipureintro; exact ⟨hw', hc'⟩
    iapply wp_value'
    iapply HΦ $$ %(rdErr e) HF
    iexists st.fs.metaLog.length
    isplitr
    · ipureintro; exact hwn st hw hQ
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
    (fun _ => .reading (.only []) 0 []) (fun _ b => NameOk b) True (fun _ => True)
    (fun _ _ _ _ => by iintro _ _; ipureintro; trivial)
    (fun st df u s r b _ _ hph' _ hcur hsb _ =>
      ⟨hok st _ _ _ (phOkS_seen hph' hph hcur), phOkS_seen hph' hph hcur b hsb⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun st df u s r _ _ hph' _ hcur => hok st _ _ _ (phOkS_seen hph' hph hcur))
    (fun _ _ _ => trivial)
    hph hE hE' Φ $$ Hinv Hsi Hfd []
  · iempintro
  iintro %v - ⟨%n, -, Hv⟩
  iapply HΦ
  icases Hv with (⟨%b, ⟨%hv, %hb⟩, Hfd⟩ | ⟨⟨%hv, -⟩, Hfd⟩ | ⟨%e, %he, Hfd⟩)
  · ileft; iexists b; iframe Hfd; ipureintro; exact ⟨hv, hb⟩
  · iright; ileft; iframe Hfd; ipureintro; exact hv
  · iright; iright; iexists e; iframe Hfd; ipureintro; exact he

/-- A claim's names are the tree's. -/
theorem entry_of_namesOf {st : OsState} {j : Ino} {N : NameSet} {h : NamesH}
    (hh : h = namesOf (st.fs.treeDur, st.fs.metaLog) j N) {b : GoString} (hb : N.Mem b) :
    st.tree.entry j b = h.cur !! b := by
  rw [hh]
  simp only [namesOf]
  rw [restrictN_lookup _ _ _ hb, entsOf_lookup]
  rfl

/-- Nothing from a claim's `next` on wrote its names. -/
theorem noWrite_of_next {st : OsState} {j : Ino} {N : NameSet} {h : NamesH} {r0 : Nat}
    (hh : h = namesOf (st.fs.treeDur, st.fs.metaLog) j N) (hr : h.next ≤ r0) :
    ∀ x (e : LogEntry), r0 ≤ x → st.fs.metaLog[x]? = some e → ∀ b, N.Mem b → ¬ e.op.Writes j b := by
  intro x e hx he b hb hw
  have := lt_namesOf_next (V := (st.fs.treeDur, st.fs.metaLog)) he hb hw
  rw [← hh] at this
  omega

theorem present_of_entry {st : OsState} (hw : FsTreeWf st) {j : Ino} {b : GoString}
    (h : (st.tree.entry j b).isSome) : present st j b = true := by
  obtain ⟨htw, -, -⟩ := wf_tree hw
  cases he : st.tree.entry j b with
  | none => rw [he] at h; cases h
  | some n =>
    have := (htw.2.2.1 j b n he).1
    simp [present, this, he]

theorem wp_osDirReadNextS' (R : Roots) (fd : w64) (j : Ino) (N : NameSet) (r0 : Nat)
    (rs : List GoString) (fresh : Bool) (dq : DFrac) (h : NamesH)
    (hfr : fresh = true → rs = []) (hr0 : fresh = false → h.next ≤ r0)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗
      osDirFdS (L := L) fd j (if fresh then .idle else .reading N r0 rs) -∗
      osNames (L := L) j N dq h -∗
      (∀ v, osNames (L := L) j N dq h -∗
        (∃ r0', ⌜fresh = false → r0' = r0⌝ ∗ ⌜fresh = true → h.next ≤ r0'⌝ ∗
          ((∃ b, ⌜v = rdName b ∧ NameOk b ∧ (N.Mem b → (h.cur !! b).isSome ∧ b ∉ rs)⌝ ∗
              osDirFdS (L := L) fd j (.reading N r0' (b :: rs))) ∨
           (⌜v = rdEnd ∧ ∀ b, N.Mem b → (h.cur !! b).isSome → b ∈ rs⌝ ∗
              osDirFdS (L := L) fd j .done) ∨
           (∃ e : w64, ⌜e ≠ 0 ∧ v = rdErr e⌝ ∗ osDirFdS (L := L) fd j (.reading N r0' rs)))) -∗
        Φ v) -∗
      WP (ExternalOp fsExt.name "DirReadNext" (Val (#fd))) @ s; E {{ Φ }} := by
  let ph : DirPhS := if fresh then .idle else .reading N r0 rs
  let r0F : Nat → Nat := fun n => if fresh then n else r0
  let Q : OsState → Prop := fun st => h = namesOf (st.fs.treeDur, st.fs.metaLog) j N
  have hnd : ph ≠ .done := by cases fresh <;> simp [ph]
  -- the read as the step finds it: at `idle`, begun now; else as it was
  have hstart : ∀ st (df : OsDirFd) u s r, FsTreeWf st → PhOkS st j ph df.rd → Q st →
      df.rd.cur st j = some (u, s, r) →
      (∀ b, N.Mem b → u b = present st j b ∧ s b = present st j b ∧ r b = decide (b ∈ rs)) ∧
      (∀ b, s b = true → NameOk b) := by
    intro st df u s r hw hph hQ hcur
    refine ⟨?_, phOkS_seen hph hnd hcur⟩
    cases hf : fresh with
    | true =>
      simp only [ph, hf, if_true] at hph
      cases hrd : df.rd with
      | idle =>
        rw [hrd] at hcur
        simp only [OsDirRead.cur, Option.some.injEq, Prod.mk.injEq] at hcur
        obtain ⟨rfl, rfl, rfl⟩ := hcur
        intro b _
        simp [hfr hf]
      | _ => rw [hrd] at hph; simp [PhOkS] at hph
    | false =>
      simp only [ph, hf] at hph
      cases hrd : df.rd with
      | reading u' s' r' =>
        rw [hrd] at hcur hph
        simp only [OsDirRead.cur, Option.some.injEq, Prod.mk.injEq] at hcur
        obtain ⟨rfl, rfl, rfl⟩ := hcur
        exact hph.2.2 (noWrite_of_next hQ (hr0 hf))
      | _ => rw [hrd] at hph; simp [PhOkS] at hph
  have hok : ∀ st (u s r : GoString → Bool) (rs' : List GoString), FsTreeWf st → Q st →
      (∀ b, N.Mem b → u b = present st j b ∧ s b = present st j b ∧ r b = decide (b ∈ rs')) →
      (∀ b, s b = true → NameOk b) → (fresh = false → r0 ≤ st.fs.metaLog.length) →
      PhOkS st j (.reading N (r0F st.fs.metaLog.length) rs') (.reading u s r) := by
    intro st u s r rs' hw hQ hm hs hle
    refine ⟨?_, hs, fun _ => hm⟩
    by_cases hf : fresh = true
    · simp [r0F, hf]
    · have hf' : fresh = false := by simpa using hf
      simp only [r0F, hf', Bool.false_eq_true, if_false]
      exact hle hf'
  have hle : ∀ st rd, PhOkS st j ph rd → fresh = false → r0 ≤ st.fs.metaLog.length := by
    intro st rd hph hf
    simp only [ph, hf, Bool.false_eq_true, if_false] at hph
    cases rd <;> simp [PhOkS] at hph
    exact hph.1
  iintro #Hinv #Hsi Hfd Hn HΦ
  iapply wp_dirReadS R fd j ph (osNames (L := L) j N dq h) Q
    (fun n b => .reading N (r0F n) (b :: rs)) (fun n => .reading N (r0F n) rs)
    (fun _ b => NameOk b ∧ (N.Mem b → (h.cur !! b).isSome ∧ b ∉ rs))
    (∀ b, N.Mem b → (h.cur !! b).isSome → b ∈ rs) (fun n => h.next ≤ n)
    (fun st Γn _ hcoh => osNames_auth L hcoh j N dq h)
    (fun st df u s r b hw _ hph hQ hcur hsb hrb => by
      obtain ⟨hm, hs⟩ := hstart st df u s r hw hph hQ hcur
      refine ⟨hok st u s _ (b :: rs) hw hQ (fun b' hb' => ?_) hs ?_, hs b hsb, fun hb => ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hm b' hb'
        refine ⟨h1, h2, ?_⟩
        rw [h3]; by_cases hbb : b' = b <;> simp [hbb]
      · exact hle st _ hph
      · obtain ⟨-, h2, h3⟩ := hm b hb
        rw [h2] at hsb
        rw [← entry_of_namesOf hQ hb]
        refine ⟨?_, ?_⟩
        · simp only [present, Bool.and_eq_true] at hsb; exact hsb.2
        · rw [h3] at hrb; simpa using hrb)
    (fun st df u s r hw _ hph hQ hcur hall => by
      obtain ⟨hm, -⟩ := hstart st df u s r hw hph hQ hcur
      intro b hb hsome
      rw [← entry_of_namesOf hQ hb] at hsome
      obtain ⟨h1, -, h3⟩ := hm b hb
      have hp := present_of_entry hw hsome
      have := hall b (by rw [h1]; exact hp) hp
      rw [h3] at this; simpa using this)
    (fun st df u s r hw _ hph hQ hcur => by
      obtain ⟨hm, hs⟩ := hstart st df u s r hw hph hQ hcur
      exact hok st u s r rs hw hQ hm hs (hle st _ hph))
    (fun st _ hQ => by rw [hQ]; exact namesOf_next_le _ _ _)
    hnd hE hE' Φ $$ Hinv Hsi Hfd Hn
  iintro %v Hn ⟨%n, %hn, Hv⟩
  iapply HΦ $$ %v Hn
  iexists r0F n
  isplitr
  · ipureintro; intro hf; simp [r0F, hf]
  isplitr
  · ipureintro; intro hf; simp only [r0F, hf, if_true]; exact hn
  icases Hv with (⟨%b, ⟨%hv, %hb⟩, Hfd⟩ | ⟨⟨%hv, %hd⟩, Hfd⟩ | ⟨%e, %he, Hfd⟩)
  · ileft; iexists b; iframe Hfd; ipureintro; exact ⟨hv, hb⟩
  · iright; ileft; iframe Hfd; ipureintro; exact ⟨hv, hd⟩
  · iright; iright; iexists e; iframe Hfd; ipureintro; exact he

end specs

end Fs
end Perennial

end
