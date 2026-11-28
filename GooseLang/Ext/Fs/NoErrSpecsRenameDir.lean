/-
What the program logic may use of the premise **no I/O error** (`NoIoErr`) on `rename(2)` of a
directory in the shared mode (wal-safe, 2026-11-21; ledger 2026-11-21, `renameWALUnlock.spec`): the
directory `d/bs` renamed to the free name `d/bt` of the same claim, by a call holding the whole call
permission, has a success (`renameDir_succ`: the source a directory, the target absent, not under the
source, no other call on the root), so under `NoIoErr` its step returns errno 0 and logs the rename
(`wp_osRenameDirSNE`). `wp_osRenameDirSW`: `wp_osRenameDirS` with its error witnessed, as
`wp_osRenameFileSW` (`NoErrSpecsRename.lean`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.NoErrSpecsRename

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section step
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]

/-- A sibling is not under a directory. -/
theorem not_isUnder_sibling (d bs bt : GoString) (hbs : NameOk bs) (hbt : NameOk bt) (hne : bs ≠ bt) :
    ¬ IsUnder (child d bs) (child d bt) := by
  rintro (h | ⟨u, hu⟩)
  · exact hne (child_eq hbs hbt h.symm).2
  · simp only [child, List.append_assoc, List.cons_append] at hu
    have hu' := List.append_cancel_left hu
    simp only [List.cons.injEq, _root_.true_and] at hu'
    exact hbt.2.2.2.1 (by rw [← hu']; simp)

/-- **`rename(2)` of the directory `d/bs` to the absent `d/bt` has a success**, when no other call is in
flight on its root. -/
theorem renameDir_succ {st : OsState} {d bs bt : GoString} {j J : Ino} {k s0 : Nat}
    (hw : FsTreeWf st) (hcall : st.proc.calls !! k = some (s0, child d bs))
    (hd : st.lookup d = some (.dir j)) (hbs : NameOk bs) (hbt : NameOk bt) (hne : bs ≠ bt)
    (hsrc : st.tree.entry j bs = some (.dir J)) (htgt : st.tree.entry j bt = none)
    (hsole : ∀ k' s', st.proc.calls !! k' = some s' → st.SameRoot (child d bs) s'.2 → k' = k) :
    ∃ st'', IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))) st
      (Val (#(0 : w64))) st'' := by
  have hls : st.lookup (child d bs) = some (.dir J) := by
    rw [lookup_child hw.roots hd hbs, hsrc]
  have hlt : st.lookup (child d bt) = none := by
    rw [lookup_child hw.roots hd hbt, htgt]
  have hneq : child d bs ≠ child d bt := fun heq => hne (child_eq hbs hbt heq).2
  have hex : (∃ J, st.lookup (child d bs) = some (.dir J)) →
      ∀ k' s' p', st.proc.calls !! k' = some (s', p') → k' = k ∨ ¬ st.SameRoot (child d bs) p' :=
    fun _ k' s' p' hk => (Classical.em (st.SameRoot (child d bs) p')).elim
      (fun hs => .inl (hsole k' (s', p') hk hs)) .inr
  have hok : RenameOk st (child d bs) (child d bt) := by
    refine ⟨hneq, ⟨_, parent_child hd hbs⟩, ⟨_, parent_child hd hbt⟩, ?_⟩
    rw [hls]
    exact ⟨not_isUnder_sibling d bs bt hbs hbt hne, .inl hlt⟩
  have hop : RenameOp st (child d bs) (child d bt)
      (.rename j bs j bt (.dir J) (st.lookup (child d bt))) :=
    ⟨j, bs, j, bt, .dir J, parent_child hd hbs, parent_child hd hbt, hls, rfl⟩
  exact ⟨_, child d bs, child d bt, k, s0, rfl, treeName_child hd hbs, treeName_child hd hbt,
    sameRoot_child_child hd, hcall, hex, .inl ⟨hok, _, hop, .inl ⟨rfl, rfl⟩⟩⟩

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`rename(2)` of the directory `d/bs` (inode `J`) to the free `d/bt` with no error** (shared mode,
the claim whole, the whole call permission; `wp_osRenameDirS'` under `NoIoErr`, a path covered, both
fitting): the rename logged, errno 0. -/
theorem wp_osRenameDirSNE (Sio : IoSet) [FsStepSat (NoIoErr Sio)] (R : Roots) (d bs bt : GoString)
    (j J : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) (k s0 : Nat) (hbs : NameOk bs)
    (hbt : NameOk bt) (hN : N.Mem bs) (hN' : N.Mem bt) (hne : bs ≠ bt)
    (hsrc : h.cur !! bs = some (.dir J)) (htgt : h.cur !! bt = none)
    (hS : Sio.path (child d bs) ∨ Sio.path (child d bt))
    (hfit : PathFits (child d bs) ∧ PathFits (child d bt)) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osCallS (L := L) k s0 (child d bs) 1 -∗
      (osCallPerm (L := L) (callKey R d) 1 -∗ osPathS (L := L) R d dq j -∗
        (∃ x, osLogged (L := L) x ⟨.rename j bs j bt (.dir J) none, s0⟩ ∗
          osNames (L := L) j N (DFrac.own 1) (h.log x ⟨.rename j bs j bt (.dir J) none, s0⟩
            (restrictN N (<[bt := .dir J]> (GMap.delete bs h.cur))))) -∗
        Φ (#(0 : w64))) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} := by
  have hNe : N ≠ .only [] := fun h0 => by rw [h0] at hN; simp [NameSet.Mem] at hN
  let o : MetaOp := .rename j bs j bt (.dir J) none
  let cl : List ClaimW := [(j, N, h, restrictN N (<[bt := .dir J]> (GMap.delete bs h.cur)))]
  have hm1 : (j, N, h, restrictN N (<[bt := .dir J]> (GMap.delete bs h.cur))) ∈ cl :=
    List.mem_singleton_self _
  have hsrcE : ∀ st, ClaimsAt st cl → st.tree.entry j bs = some (.dir J) := fun st hat => by
    rw [hat.ent _ hm1 bs hN]; exact hsrc
  have htgtE : ∀ st, ClaimsAt st cl → st.tree.entry j bt = none := fun st hat => by
    rw [hat.ent _ hm1 bt hN']; exact htgt
  have hneq : child d bs ≠ child d bt := fun heq => hne (child_eq hbs hbt heq).2
  have hsoleOf : ∀ st, FsTreeWf st → st.fs.roots = R →
      ((1 : Qp) = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R (child d bs) → k' = k) →
      ∀ k' s', st.proc.calls !! k' = some s' → st.SameRoot (child d bs) s'.2 → k' = k :=
    fun st hw hR hsole k' s' hk' hs =>
      hsole rfl k' s' hk' (by rw [← hR]; exact callKey_of_sameRoot hw.roots hs)
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, child d bs) →
      ((1 : Qp) = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R (child d bs) → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))) st
        e' st' ∧ FilesSame st st' := by
    intro st hw hR hcall hsole hp _
    exact ⟨_, _, renameStep_err hp hp hbs hbt (sameRoot_child_child hp) hcall
      (fun _ k' s' hk' hs => hsoleOf st hw hR hsole k' s' hk' hs), filesSame_metaEnd st k⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, child d bs) →
      ((1 : Qp) = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R (child d bs) → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))) st e' st' →
      (∃ hh hh', ExtSemantics.step (E := fsExt) GoLocalContext.typeFns "Rename"
        (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))) hh st () e' hh' st' ()) →
      ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ (fun w lg => w = #(0 : w64) ∧ lg = true) w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧
          (fun w lg => w = #(0 : w64) ∧ lg = true) w true)) := by
    intro st e' st' hw hR hcall hsole hp hat Hst Hsem
    obtain ⟨hh, hh', Hsem⟩ := Hsem
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    have hz : e' = Val (#(0 : w64)) := by
      obtain ⟨st'', hst''⟩ := renameDir_succ hw hcall hp hbs hbt hne (hsrcE st hat) (htgtE st hat)
        (hsoleOf st hw hR hsole)
      exact noIoErr_step (Sio := Sio) Hsem
        (by simp only [IoCovers]; exact ⟨k, child d bs, child d bt, rfl, hS, hfit.1, hfit.2⟩)
        ⟨_, st'', hst'', rfl⟩
    obtain ⟨e, rfl, hr⟩ := renameStep_cases hw hcall hp hp hbs hbt (hsrcE st hat) hneq Hst
    have he0 : e = 0 := by
      injection hz with hz'
      exact go.intoVal_inj hz'
    subst he0
    rw [htgtE st hat] at hr
    rcases hr with ⟨rfl, he⟩ | rfl
    · exact absurd rfl he
    · refine ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, fun x hx => ?_, rfl, rfl⟩⟩
      rcases mem_rename _ _ _ _ _ _ _ _ hx with rfl | rfl | hx
      · exact hlt _ (mem_of_reach htw (reach_of_lookup hp))
      · exact hlt _ (mem_of_reach htw (reach_of_lookup hp))
      · exact hlt _ hx
  have htree : ∀ st, FsTreeWf st → st.fs.roots = R → st.lookup d = some (.dir j) → ClaimsAt st cl →
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) ∧
      (∃ rj ∈ R, IsUnder rj.1 (child d bs) ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1) := by
    intro st hw hR hp hat
    obtain ⟨htw, -, -⟩ := wf_tree hw
    have hjm := mem_of_reach htw (reach_of_lookup hp)
    have hss : st.lookup (child d bs) = some (.dir J) := by
      rw [lookup_child hw.roots hp hbs]; exact hsrcE st hat
    have hnot : ¬ BelowP st.tree J j := fun hb =>
      not_isUnder_child_self d bs (isUnder_of_belowP hw.roots htw hss hp hb)
    refine ⟨hR ▸ treeWf_renameDir htw (reach_of_lookup hp) (reach_of_lookup hp) hbt (hsrcE st hat)
        (fun h0 => hne h0.2) (.inl (htgtE st hat)) hnot _ _,
      named_rename _ _ _ _ _ _ _, fun x hx => ?_, fun J hJ => by simp [o, MetaOp.newDirs] at hJ,
      fun hnd => absurd (by simp [o, MetaOp.IsDirOp]) hnd, fun c hc => ?_,
      rootClause_one hR hp bs (by simp [cl])⟩
    · rcases mem_rename _ _ _ _ _ _ _ _ hx with rfl | rfl | hx
      · exact .inl hjm
      · exact .inl hjm
      · exact .inl hx
    · rw [List.mem_singleton] at hc; subst hc
      apply restrictN_eq_of
      intro b hb
      rw [entsOf_lookup, entry_rename, hsrcE st hat]
      show (if j = j ∧ bt = b then some (Node.dir J) else if j = j ∧ bs = b then none
        else st.tree.entry j b) = _
      by_cases hbt' : bt = b
      · subst hbt'; rw [if_pos ⟨rfl, rfl⟩, GMap.lookup_insert]
      · rw [if_neg (fun h0 => hbt' h0.2), GMap.lookup_insert_ne _ _ hbt']
        by_cases hbs' : bs = b
        · subst hbs'; simp
        · rw [if_neg (fun h0 => hbs' h0.2), GMap.lookup_delete_ne _ hbs', hat.ent _ hm1 b hb]
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_logStepSQ "Rename" _ (by simp [val.isPanic]) R k s0 (child d bs) 1 o cl
    (osPathS (L := L) R d dq j) (fun st => st.lookup d = some (.dir j))
    (fun w lg => w = #(0 : w64) ∧ lg = true)
    (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact hNe)
    (fun c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨bs, hN, .inl (by simp [o, MetaOp.slots])⟩)
    (fun sl hsl => by
      simp only [o, MetaOp.slots, List.mem_cons, List.mem_nil_iff, or_false] at hsl
      rcases hsl with rfl | rfl
      · exact ⟨_, hm1, rfl, hN⟩
      · exact ⟨_, hm1, rfl, hN'⟩)
    (fun _ _ => .inr rfl) (fun _ => rfl)
    (fun j0 b hb => by
      simp only [o, MetaOp.adds] at hb
      split at hb
      · simp at hb; subst hb; exact hbt
      · simp at hb)
    (fun st Γn hR hcoh => pathS_of R d dq j st Γn hR hcoh) hprog hpost
    (fun st e' st' hw _ hcall _ hp hat Hst => by
      obtain ⟨e, rfl, hr⟩ := renameStep_cases hw hcall hp hp hbs hbt (hsrcE st hat) hneq Hst
      rcases hr with ⟨rfl, -⟩ | rfl
      · exact filesSame_metaEnd st k
      · exact (loggedFrom_metaDo st k s0 _).same)
    htree hE hE' Φ $$ Hinv Hsi Hp [Hn] Hk
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hn
  iintro %w Hq Hp Hpost
  icases Hpost with (⟨%hW, -⟩ | ⟨%hW, %x, Hlg, Hl, -⟩)
  · exact absurd hW.2 (by simp)
  · obtain ⟨rfl, -⟩ := hW
    icases osCallPerm_unchild R d bs _ j _ $$ Hp Hq with ⟨Hp, Hq⟩
    iapply HΦ $$ Hq Hp
    iexists x
    isplitl [Hlg]
    · iexact Hlg
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl

/-- **`rename(2)` of the directory `d/bs` to the free `d/bt`, its error witnessed** (`wp_osRenameDirS`):
an errno only when the file system can fail on the target's path, or a path does not fit. -/
theorem wp_osRenameDirSW (R : Roots) (d bs bt : GoString) (j J : Ino) (N : NameSet) (dq : DFrac)
    (h : NamesH) (k s0 : Nat) (hbs : NameOk bs) (hbt : NameOk bt) (hN : N.Mem bs) (hN' : N.Mem bt)
    (hne : bs ≠ bt) (hsrc : h.cur !! bs = some (.dir J)) (htgt : h.cur !! bt = none)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osCallS (L := L) k s0 (child d bs) 1 -∗
      (∀ e : w64, osCallPerm (L := L) (callKey R d) 1 -∗ osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j N h ⟨.rename j bs j bt (.dir J) none, s0⟩
          (<[bt := .dir J]> (GMap.delete bs h.cur)) (e ≠ 0) -∗
        ⌜e ≠ 0 → ¬ (FsNoErrOn (· = child d bt) ∧ PathFits (child d bs) ∧ PathFits (child d bt))⌝ -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} := by
  iintro #Hos #Hsi Hp Hn Hk HΦ
  by_cases hW : FsNoErrOn (· = child d bt) ∧ PathFits (child d bs) ∧ PathFits (child d bt)
  · obtain ⟨⟨Sio, -, h1, -, hp⟩, hf1, hf2⟩ := hW
    iapply wp_osRenameDirSNE Sio R d bs bt j J N dq h k s0 hbs hbt hN hN' hne hsrc htgt
      (.inr (hp _ rfl)) ⟨hf1, hf2⟩ hE hE' Φ $$ Hos Hsi Hp Hn Hk
    iintro Hperm Hp Hl
    iapply HΦ $$ Hperm Hp [Hl]
    · unfold osNamesAfter; iright; iexact Hl
    ipureintro; intro h0; exact absurd rfl h0
  · iapply wp_osRenameDirS R d bs bt j J N dq h k s0 hbs hbt hN hN' hne hsrc htgt hE hE' Φ
      $$ Hos Hsi Hp Hn Hk
    iintro %e Hperm Hp Hres
    iapply HΦ $$ Hperm Hp Hres
    ipureintro; intro _; exact hW

end specs

end Fs
end Perennial

end
