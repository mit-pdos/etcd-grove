/-
The shared mode of the tree: `open(2)` with `O_CREAT` of a name `b` of a claim on any names `N`
containing it (`wp_osOpenCreateSN`), `TreeSharedCreate.lean`'s `wp_osOpenCreateS'` with the claim
generalized from `.only [b]` (the WAL's `Repair` creates `<segment>.wal.broken` in the WAL directory's
claim on all but the pipeline's names; `notes/wal-fsext-plan.md`, W7-W12 log, ninth session). The
proof is that one's, with `N`'s other names unchanged by the create. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedCreate

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

/-- **`open(2)` with `O_CREAT` of `d/b`, `b` a name of the claim on `N`** (shared mode), the claim
whole: the file there opened, or (`b` absent) a new one created, its `create` logged in the claim. -/
theorem wp_osOpenCreateSN (R : Roots) (d b : GoString) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat) (hcr : fl.toNat / O_CREAT % 2 = 1)
    (htr : fl.toNat / O_TRUNC % 2 = 0 ∨ h.cur !! b = none) (hb : NameOk b) (hN : N.Mem b) (hnd : ∀ J, h.cur !! b ≠ some (.dir J))
    (hs : h.next ≤ s0) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (N) (DFrac.own 1) h -∗ osCallS (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        ((∃ i, ⌜h.cur !! b = some (.file i)⌝ ∗ osNames (L := L) j (N) (DFrac.own 1) h ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))) ∨
         (⌜h.cur !! b = none⌝ ∗ ∃ x i, osLogged (L := L) x (⟨.create j b i, s0⟩ : LogEntry) ∗
            osNames (L := L) j (N) (DFrac.own 1) (h.log x (⟨.create j b i, s0⟩ : LogEntry) (<[b := .file i]> h.cur)) ∗
            osMeta (L := L) i (DFrac.own 1) newMeta ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ osNames (L := L) j (N) (DFrac.own 1) h)) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  have hbN : N.Mem b := hN
  let oF : Nat → MetaOp := fun n => .create j b n
  let cl : List ClaimW := [(j, N, h, ∅)]
  let curF : Nat → ClaimW → Ents := fun n _ => <[b := .file n]> h.cur
  let W : val → Bool → Prop := fun w lg =>
    ∃ fd e : w64, w = PairV (#fd) (#e) ∧ (lg = true → h.cur !! b = none)
  have hentE : ∀ st, ClaimsAt st cl → st.tree.entry j b = h.cur !! b := fun st hat =>
    hat.ent _ (List.mem_singleton_self _) b hbN
  have hndE : ∀ st, ClaimsAt st cl → ∀ J, st.tree.entry j b ≠ some (.dir J) := by
    intro st hat J; rw [hentE st hat]; exact hnd J
  have htrE : ∀ st, ClaimsAt st cl → fl.toNat / O_TRUNC % 2 = 0 ∨ st.tree.entry j b = none :=
    fun st hat => htr.imp id (fun hn => (hentE st hat).trans hn)
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st' ∧
        FilesSame st st' := by
    intro st hw _ hcall _ hp hat
    refine ⟨_, st.metaEnd k, .inl ⟨child d b, fl, k, s0, rfl, .inr (treeName_child hp hb), hfl,
      hcall, ⟨fun htr1 i hl => ?_, .inr ⟨1, by decide, fun h => absurd h (by decide), rfl, .inl rfl⟩⟩⟩, filesSame_metaEnd st k⟩
    rcases htr with htr | hnone
    · have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = false := by simp [htr]
      exact (Bool.false_ne_true (htr'.symm.trans htr1)).elim
    · have hl0 : (st.metaEnd k).lookup (child d b) = st.tree.entry j b :=
        lookup_child hw.roots hp hb
      have hl' : (st.metaEnd k).lookup (child d b) = some (.file i) := hl
      rw [hl0, hentE st hat, hnone] at hl'; cases hl'
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st' →
      ∃ w, e' = Val w ∧ FsTreeWf st' ∧
        ((EndedT st st' k ∧ W w false) ∨ (LoggedT st st' k s0 (oF st.fs.nextIno) ∧ W w true)) := by
    intro st e' st' hw _ hcall _ hp hat Hst
    rcases openCreateStep_cases hcr (htrE st hat) hw hcall hp hb (hndE st hat) Hst with
      ⟨e, -, rfl, rfl⟩ | ⟨i, fd, -, hfree, rfl, rfl⟩ | ⟨hen, e, -, rfl, rfl⟩ | ⟨hen, fd, hfree, rfl, rfl⟩
    · exact ⟨_, rfl, fsTreeWf_metaEnd hw k,
        .inl ⟨endedT_metaEnd st k, _, _, rfl, fun h => by cases h⟩⟩
    · exact ⟨_, rfl, fsTreeWf_addFd (fsTreeWf_metaEnd hw k) hfree.2.2.1,
        .inl ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, _, _, rfl, fun h => by cases h⟩⟩
    · exact ⟨_, rfl, fsTreeWf_created hw k s0 (reach_of_lookup hp) hb hen,
        .inr ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, _, _, rfl, fun _ => (hentE st hat).symm.trans hen⟩⟩
    · exact ⟨_, rfl, fsTreeWf_addFd (fsTreeWf_created hw k s0 (reach_of_lookup hp) hb hen)
          (createdSt_dfds_none hfree.2.2.1),
        .inr ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, _, _, rfl, fun _ => (hentE st hat).symm.trans hen⟩⟩
  have hworld : ∀ st e' st' (hh hh' : GMap Loc (NonAtomic val)) Γb Γm Γf Γt w lg, FsTreeWf st →
      st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st' →
      e' = Val w → W w lg → (lg = false → EndedT st st' k) →
      (lg = true → LoggedT st st' k s0 (oF st.fs.nextIno)) →
      HeapRendered st st' hh hh' → MapsFresh st st' hh →
      ⊢ osWorld (L := L) st Γb Γm Γf Γt hh ==∗ ∃ Γb' Γm' Γf' Γt',
        osWorld (L := L) st' Γb' Γm' Γf' Γt' hh' ∗ ocGift (L := L) fl h.cur b st.fs.nextIno w lg := by
    intro st e' st' hh hh' Γb Γm Γf Γt w lg hw _ hcall _ hp hat Hst hew _ hend hlog Hr Hfr
    rcases openCreateStep_cases hcr (htrE st hat) hw hcall hp hb (hndE st hat) Hst with
      ⟨e, he, rfl, rfl⟩ | ⟨i, fd, hen, hfree, rfl, rfl⟩ | ⟨hen, e, he, rfl, rfl⟩ | ⟨hen, fd, hfree, rfl, rfl⟩
    · cases lg with
      | true => exact absurd (hlog rfl) (fun h' => not_loggedT_same h' rfl)
      | false =>
        injection hew with hew; subst hew
        iintro Hw
        imod osWorld_filesSame (filesSame_metaEnd st k) Hr Hfr $$ Hw with Hw
        imodintro
        iexists Γb, Γm, Γf, Γt
        isplitl [Hw]
        · iexact Hw
        unfold ocGift
        iexists (-1 : w64), e
        isplitr
        · ipureintro; rfl
        iright; isplitr
        · ipureintro; rfl
        iright; ipureintro; exact ⟨he, rfl⟩
    · cases lg with
      | true => exact absurd (hlog rfl) (fun h' => not_loggedT_same h' rfl)
      | false =>
        injection hew with hew; subst hew
        iintro Hw
        imod osWorld_addFd (filesSame_metaEnd st k) (d := openFd i fl) hfree.2.1
          (file_of_entry hw hen) Hr Hfr $$ Hw with ⟨Hw, Hfd⟩
        imodintro
        iexists Γb, Γm, _, Γt
        isplitl [Hw]
        · iexact Hw
        unfold ocGift
        iexists fd, (0 : w64)
        isplitr
        · ipureintro; rfl
        iright; isplitr
        · ipureintro; rfl
        ileft; iexists i
        isplitr
        · ipureintro; rw [← hentE st hat]; exact hen
        unfold ocFd
        iright
        isplitr
        · ipureintro; exact ⟨rfl, hfree.1⟩
        · iexact Hfd
    · cases lg with
      | false => exact absurd (hend rfl) (fun h' => not_endedT_snoc h' rfl)
      | true =>
        injection hew with hew; subst hew
        iintro Hw
        imod osWorld_created hw k j b s0 $$ Hw with ⟨Hw, Hm⟩
        imod osWorld_filesSame (filesSame_refl _) Hr Hfr $$ Hw with Hw
        imodintro
        iexists Γb, _, Γf, Γt
        isplitl [Hw]
        · iexact Hw
        unfold ocGift
        iexists (-1 : w64), e
        isplitr
        · ipureintro; rfl
        ileft
        isplitr
        · ipureintro; rfl
        isplitl [Hm]
        · iexact Hm
        unfold ocFd
        ileft; ipureintro; exact ⟨he, rfl⟩
    · cases lg with
      | false => exact absurd (hend rfl) (fun h' => not_endedT_snoc h' rfl)
      | true =>
        injection hew with hew; subst hew
        iintro Hw
        imod osWorld_created hw k j b s0 $$ Hw with ⟨Hw, Hm⟩
        imod osWorld_addFd (st := createdSt st k j b s0) (filesSame_refl _) (fd := fd)
          (d := openFd st.fs.nextIno fl) hfree.2.1 ⟨_, file_setFile_eq _ _ _⟩ Hr Hfr
          $$ Hw with ⟨Hw, Hfd⟩
        imodintro
        iexists Γb, _, _, Γt
        isplitl [Hw]
        · iexact Hw
        unfold ocGift
        iexists fd, (0 : w64)
        isplitr
        · ipureintro; rfl
        ileft
        isplitr
        · ipureintro; rfl
        isplitl [Hm]
        · iexact Hm
        unfold ocFd
        iright
        isplitr
        · ipureintro; exact ⟨rfl, hfree.1⟩
        · iexact Hfd
  have htree : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e' st' →
      LoggedT st st' k s0 (oF st.fs.nextIno) →
      let o := oF st.fs.nextIno
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = curF st.fs.nextIno c) := by
    intro st e' st' hw _ hcall hp hat Hst hlf
    have hen : st.tree.entry j b = none := by
      rcases openCreateStep_cases hcr (htrE st hat) hw hcall hp hb (hndE st hat) Hst with
        ⟨_e, _he, _he', hst'⟩ | ⟨_i, _fd, _h1, _h2, _h3, hst'⟩ | ⟨hen, -⟩ | ⟨hen, -⟩
      · exact absurd hlf (fun h' => not_loggedT_same h' (by rw [hst']; rfl))
      · exact absurd hlf (fun h' => not_loggedT_same h' (by rw [hst']; rfl))
      · exact hen
      · exact hen
    obtain ⟨htw, -, -⟩ := wf_tree hw
    have hjm : j ∈ st.tree := mem_of_reach htw (reach_of_lookup hp)
    have hnf := files_next_none hw
    refine ⟨fun x hx => ?_, fun J hJ => by simp [oF, MetaOp.newDirs] at hJ,
      fun _ => ⟨⟨hjm, hen⟩, ?_⟩, fun c hc => ?_⟩
    · simp only [oF, MetaOp.apply] at hx
      rw [mem_upd] at hx
      rcases hx with rfl | hx
      · exact .inl hjm
      · exact .inl hx
    · intro j' b' i ho t ht hnm
      simp only [oF, MetaOp.create.injEq] at ho
      obtain ⟨-, -, rfl⟩ := ho
      obtain ⟨f, hf⟩ := (hw.hist t ht).2.1 _ hnm
      rw [hnf] at hf; cases hf
    · rw [List.mem_singleton] at hc; subst hc
      apply GMap.ext; intro b'
      show restrictN (N) (entsOf _ j) !! b' = (<[b := .file st.fs.nextIno]> h.cur) !! b'
      by_cases hb' : N.Mem b'
      · rw [restrictN_lookup _ _ _ hb', entsOf_lookup, entry_create]
        by_cases hbb : b = b'
        · subst hbb; rw [if_pos ⟨rfl, rfl⟩, GMap.lookup_insert]
        · rw [if_neg (fun h => hbb h.2), GMap.lookup_insert_ne _ _ hbb]
          exact hat.ent _ (List.mem_singleton_self _) b' hb'
      · rw [restrictN_lookup_not _ _ _ hb']
        have hne : b ≠ b' := fun h => hb' (h ▸ hbN)
        rw [GMap.lookup_insert_ne _ _ hne]
        exact (hat.out _ (List.mem_singleton_self _) b' hb').symm
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_logStepSW "Open" _ (by simp [val.isPanic]) R k s0 q oF cl curF
    (osPathS (L := L) R d dq j) (fun st => st.lookup d = some (.dir j)) W (ocGift (L := L) fl h.cur b)
    (fun c hc => by
      rw [List.mem_singleton] at hc; subst hc
      show N ≠ .only []
      intro he; rw [he] at hbN; simp [NameSet.Mem] at hbN) (fun _ c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨b, hbN, .inl (by simp [oF, MetaOp.slots])⟩)
    (by intro n sl hsl; simp [oF, MetaOp.slots] at hsl; subst hsl
        exact ⟨_, List.mem_singleton_self _, rfl, hbN⟩)
    (by simp [cl, hs]) (fun _ hd => hd.elim)
    (by intro n j' b' hb'; simp [oF, MetaOp.adds] at hb'; rw [hb'.2]; exact hb)
    (fun st Γn hR hcoh => pathS_of R d dq j st Γn hR hcoh) hprog hpost hworld htree hE hE' Φ
    $$ Hinv Hsi Hp [Hn] Hk
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hn
  iintro %w Hq Hp Hpost
  icases Hpost with (⟨%hW, ⟨%n, HG⟩, Hl⟩ | ⟨%hW, %n, %x, HG, Hlg, Hl, -⟩)
  · obtain ⟨fd, e, rfl, -⟩ := hW
    unfold ocGift
    icases HG with ⟨%fd', %e', %hfe, HG⟩
    injection hfe with h1 h2
    obtain rfl := go.intoVal_inj h1
    obtain rfl := go.intoVal_inj h2
    icases HG with (⟨%hlg, -⟩ | ⟨-, HG⟩)
    · cases hlg
    iapply HΦ $$ %fd %e Hq Hp
    icases HG with (⟨%i, %hi, HG⟩ | %hf)
    · ileft
      iexists i
      isplitr
      · ipureintro; exact hi
      isplitl [Hl]
      · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
      unfold ocFd; iexact HG
    · iright; iright
      isplitr
      · ipureintro; exact hf
      iapply (BigSepL.bigSepL_singleton).1 $$ Hl
  · obtain ⟨fd, e, rfl, hnone⟩ := hW
    unfold ocGift
    icases HG with ⟨%fd', %e', %hfe, HG⟩
    injection hfe with h1 h2
    obtain rfl := go.intoVal_inj h1
    obtain rfl := go.intoVal_inj h2
    icases HG with (⟨-, Hm, HG⟩ | ⟨%hlg, -⟩)
    · iapply HΦ $$ %fd %e Hq Hp
      iright; ileft
      isplitr
      · ipureintro; exact hnone rfl
      iexists x, n
      isplitl [Hlg]
      · iexact Hlg
      isplitl [Hl]
      · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
      isplitl [Hm]
      · iexact Hm
      unfold ocFd; iexact HG
    · cases hlg

end specs

end Fs
end Perennial

end
