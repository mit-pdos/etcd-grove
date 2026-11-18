/-
**`rename(2)` of a directory onto a name holding anything** (shared mode; `notes/wal-fsext-plan.md`, W4 log,
twenty-seventh session). Untrusted: a proof over the extension's step relation.

`wp_osRenameDirS` (`TreeShared.lean`) needs the target name free. The WAL's cleanup renames a WAL
directory to `nm.broken.<time>`, a name the area's claim knows but which may hold a leftover file or
directory. The model (`RenameOk`, `Impl.lean`) lets a directory replace only an empty directory there;
onto a file or a non-empty directory the call fails with no effect. `wp_osRenameDirAnyS` covers every
target `old := h.cur !! bt`: the post is the claim after the operation `.rename j bs j bt (.dir J) old`,
as `wp_osRenameDirS`'s, and on a logged outcome the target held nothing or a directory (then empty at
the step, and left unreachable: its claims, if any, keep their entries).

The tree's well-formedness of the logged operation is taken from the step (`RenameOk`'s empty target),
not from the caller's resources, so the proof goes through `wp_logStepSW`, whose tree obligations are
conditional on the step, instead of `wp_osRename1S`.
-/
module

public import GooseLang.Ext.Fs.TreeSharedMeta

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

/-- **A directory's rename step within one directory, by its outcome**: it only ended the call, with
an errno, or it logged the rename (with any errno), the target then nothing or an empty directory. -/
theorem renameDirStep_cases {st : OsState} {d bs bt : GoString} {j J : Ino}
    {k s0 : Nat} {e' : Expr} {st' : OsState} (hw : FsTreeWf st)
    (hcall : st.proc.calls !! k = some (s0, child d bs))
    (hd : st.lookup d = some (.dir j)) (hbs : NameOk bs) (hbt : NameOk bt)
    (hsrc : st.tree.entry j bs = some (.dir J)) (hne : child d bs ≠ child d bt)
    (Hst : IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))) st e' st') :
    ∃ e : w64, e' = Val (#e) ∧ ((st' = st.metaEnd k ∧ e ≠ 0) ∨
      (st' = (st.metaEnd k).metaDo (.rename j bs j bt (.dir J) (st.tree.entry j bt)) s0 ∧
        (st.tree.entry j bt = none ∨
          ∃ J2, st.tree.entry j bt = some (.dir J2) ∧ ∀ c, st.tree.entry J2 c = none))) := by
  simp only [IsFsStep] at Hst
  obtain ⟨s1, t1, k', start, hv, -, -, -, hk', -, hres⟩ := Hst
  obtain ⟨rfl, rfl, rfl⟩ := tokPair_inj hv
  have hse := calls_start hcall hk'; simp only [Prod.mk.injEq] at hse; rw [hse.1] at hres
  rcases hres with ⟨hok, o, ho, hr⟩ | ⟨hst, -, -, -⟩ | ⟨e, he, rfl, rfl⟩
  · have hss : st.lookup (child d bs) = some (.dir J) := by
      rw [lookup_child hw.roots hd hbs]; exact hsrc
    have htt : st.lookup (child d bt) = st.tree.entry j bt := lookup_child hw.roots hd hbt
    obtain ⟨-, -, -, hm⟩ := hok
    rw [hss] at hm
    obtain ⟨-, hm⟩ := hm
    have hemp : st.tree.entry j bt = none ∨
        ∃ J2, st.tree.entry j bt = some (.dir J2) ∧ ∀ c, st.tree.entry J2 c = none := by
      rcases hm with h0 | ⟨J2, hJ2, hJ2e⟩
      · exact .inl (htt ▸ h0)
      · exact .inr ⟨J2, htt ▸ hJ2, hJ2e⟩
    obtain ⟨js, bs', jt, bt', n', h1, h2, h3, rfl⟩ := ho
    rw [parent_child hd hbs] at h1; rw [parent_child hd hbt] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
    rw [hss] at h3; cases h3
    rw [htt] at hr
    rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
    · exact ⟨0, rfl, .inr ⟨rfl, hemp⟩⟩
    · exact ⟨e, rfl, .inl ⟨rfl, he⟩⟩
    · exact ⟨e, rfl, .inr ⟨rfl, hemp⟩⟩
  · exact absurd hst hne
  · exact ⟨e, rfl, .inl ⟨rfl, he⟩⟩

/-- What a logged rename found at the target (`wp_osRenameDirAnyS`'s post). -/
def RenTgtOk (old : Option Node) : Prop := old = none ∨ ∃ J2, old = some (.dir J2)

/-- **`rename(2)`** of the directory `d/bs` (inode `J`) to `d/bt`, whatever `bt` holds (`old`), by a call
holding the whole call permission: the claim after the operation, and on a logged outcome the
target nothing or a directory (`RenTgtOk`; the model replaces only an empty one). -/
theorem wp_osRenameDirAnyS (R : Roots) (d bs bt : GoString) (j J : Ino) (N : NameSet) (dq : DFrac)
    (h : NamesH) (k s0 : Nat) (hbs : NameOk bs) (hbt : NameOk bt) (hN : N.Mem bs) (hN' : N.Mem bt)
    (hne : bs ≠ bt) (hsrc : h.cur !! bs = some (.dir J))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osCallS (L := L) k s0 (child d bs) 1 -∗
      (∀ e : w64, osCallPerm (L := L) (callKey R d) 1 -∗ osPathS (L := L) R d dq j -∗
        ((⌜e ≠ 0⌝ ∗ osNames (L := L) j N (DFrac.own 1) h) ∨
         (⌜RenTgtOk (h.cur !! bt)⌝ ∗ ∃ x, osLogged (L := L) x ⟨.rename j bs j bt (.dir J) (h.cur !! bt), s0⟩ ∗
           osNames (L := L) j N (DFrac.own 1)
             (h.log x ⟨.rename j bs j bt (.dir J) (h.cur !! bt), s0⟩
               (restrictN N (<[bt := .dir J]> (GMap.delete bs h.cur)))))) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} := by
  have hNe : N ≠ .only [] := fun h0 => by rw [h0] at hN; simp [NameSet.Mem] at hN
  let old := h.cur !! bt
  let o : MetaOp := .rename j bs j bt (.dir J) old
  let cl : List ClaimW := [(j, N, h, restrictN N (<[bt := .dir J]> (GMap.delete bs h.cur)))]
  have hm1 : (j, N, h, restrictN N (<[bt := .dir J]> (GMap.delete bs h.cur))) ∈ cl :=
    List.mem_singleton_self _
  have hsrcE : ∀ st, ClaimsAt st cl → st.tree.entry j bs = some (.dir J) := fun st hat => by
    rw [hat.ent _ hm1 bs hN]; exact hsrc
  have htgtE : ∀ st, ClaimsAt st cl → st.tree.entry j bt = old := fun st hat => by
    rw [hat.ent _ hm1 bt hN']
  have hneq : child d bs ≠ child d bt := fun heq => hne (child_eq hbs hbt heq).2
  let W : val → Bool → Prop := fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0) ∧
    (lg = true → RenTgtOk old)
  -- the step's outcome, from the state the claims and the spine fix
  have hcases : ∀ st e' st', FsTreeWf st → st.proc.calls !! k = some (s0, child d bs) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))) st e' st' →
      ∃ e : w64, e' = Val (#e) ∧ ((st' = st.metaEnd k ∧ e ≠ 0) ∨
        (st' = (st.metaEnd k).metaDo o s0 ∧ (st.tree.entry j bt = none ∨
          ∃ J2, st.tree.entry j bt = some (.dir J2) ∧ ∀ c, st.tree.entry J2 c = none))) := by
    intro st e' st' hw hcall hp hat Hst
    obtain ⟨e, he, hr⟩ := renameDirStep_cases hw hcall hp hbs hbt (hsrcE st hat) hneq Hst
    refine ⟨e, he, ?_⟩
    rcases hr with h1 | ⟨h1, h2⟩
    · exact .inl h1
    · exact .inr ⟨by rw [h1, htgtE st hat], h2⟩
  have hlt : ∀ st, FsTreeWf st → st.lookup d = some (.dir j) →
      ∀ x, x ∈ o.apply st.tree → x < ((st.metaEnd k).metaDo o s0).fs.nextIno := by
    intro st hw hp x hx
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    rcases mem_rename _ _ _ _ _ _ _ _ hx with rfl | rfl | hx
    · exact hlt _ (mem_of_reach htw (reach_of_lookup hp))
    · exact hlt _ (mem_of_reach htw (reach_of_lookup hp))
    · exact hlt _ hx
  have hwf' : ∀ st, FsTreeWf st → st.lookup d = some (.dir j) → ClaimsAt st cl →
      (st.tree.entry j bt = none ∨
        ∃ J2, st.tree.entry j bt = some (.dir J2) ∧ ∀ c, st.tree.entry J2 c = none) →
      FsTreeWf ((st.metaEnd k).metaDo o s0) := by
    intro st hw hp hat ht
    obtain ⟨htw, -, -⟩ := wf_tree hw
    have hss : st.lookup (child d bs) = some (.dir J) := by
      rw [lookup_child hw.roots hp hbs]; exact hsrcE st hat
    have hnot : ¬ BelowP st.tree J j := fun hb =>
      not_isUnder_child_self d bs (isUnder_of_belowP hw.roots htw hss hp hb)
    exact (loggedFrom_metaDo st k s0 o).wf hw
      (treeWf_renameDir htw (reach_of_lookup hp) (reach_of_lookup hp) hbt (hsrcE st hat)
        (fun h0 => hne h0.2) ht hnot _ _)
      (named_rename _ _ _ _ _ _ _) (hlt st hw hp)
  have hRtgt : ∀ st, ClaimsAt st cl → (st.tree.entry j bt = none ∨
      ∃ J2, st.tree.entry j bt = some (.dir J2) ∧ ∀ c, st.tree.entry J2 c = none) → RenTgtOk old := by
    intro st hat ht
    rw [htgtE st hat] at ht
    rcases ht with h0 | ⟨J2, hJ2, -⟩
    · exact .inl h0
    · exact .inr ⟨J2, hJ2⟩
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_logStepSW "Rename" _ (by simp [val.isPanic]) R k s0 (child d bs) 1 (fun _ => o) cl (fun _ c => c.2.2.2)
    (osPathS (L := L) R d dq j) (fun st => st.lookup d = some (.dir j)) W (fun _ _ _ => emp)
    (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact hNe)
    (fun _ c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨bs, hN, .inl (by simp [o, MetaOp.slots])⟩)
    (fun _ sl hsl => by
      simp only [o, MetaOp.slots, List.mem_cons, List.mem_nil_iff, or_false] at hsl
      rcases hsl with rfl | rfl
      · exact ⟨_, hm1, rfl, hN⟩
      · exact ⟨_, hm1, rfl, hN'⟩)
    (fun _ _ => .inr rfl) (fun _ _ => rfl)
    (fun _ j0 b hb => by
      simp only [o, MetaOp.adds] at hb
      split at hb
      · simp at hb; subst hb; exact hbt
      · simp at hb)
    (fun st Γn hR hcoh => pathS_of R d dq j st Γn hR hcoh)
    (fun st hw hR hcall hsole hp hat =>
      ⟨_, _, renameStep_err hp hp hbs hbt (sameRoot_child_child hp) hcall (fun _ k' s' hk' hs =>
        hsole rfl k' s' hk' (by rw [← hR]; exact callKey_of_sameRoot hw.roots hs)), filesSame_metaEnd st k⟩)
    (fun st e' st' hw _ hcall _ hp hat Hst => by
      obtain ⟨e, rfl, hr⟩ := hcases st e' st' hw hcall hp hat Hst
      rcases hr with ⟨rfl, he⟩ | ⟨rfl, ht⟩
      · exact ⟨_, rfl, fsTreeWf_metaEnd hw k, .inl ⟨endedT_metaEnd st k, e, rfl, fun _ => he,
          (fun h0 => by cases h0)⟩⟩
      · exact ⟨_, rfl, hwf' st hw hp hat ht, .inr ⟨(loggedFrom_metaDo st k s0 o).toT, e, rfl,
          (fun h0 => by cases h0), fun _ => hRtgt st hat ht⟩⟩)
    (fun st e' st' h h' Γb Γm Γf Γt w lg hw hR hcall hsole hp hat Hst _ _ _ _ Hr Hfr => by
      have hs : FilesSame st st' := by
        obtain ⟨e, -, hr⟩ := hcases st e' st' hw hcall hp hat Hst
        rcases hr with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact filesSame_metaEnd st k
        · exact (loggedFrom_metaDo st k s0 o).same
      iintro Hw
      imod osWorld_filesSame hs Hr Hfr $$ Hw with Hw
      imodintro
      iexists Γb, Γm, Γf, Γt
      iframe)
    (fun st e' st' hw hR hcall hp hat _ _ => by
      obtain ⟨htw, -, -⟩ := wf_tree hw
      have hjm := mem_of_reach htw (reach_of_lookup hp)
      refine ⟨fun x hx => ?_, fun J hJ => by simp [o, MetaOp.newDirs] at hJ,
        fun _ => ⟨⟨hjm, hjm, hsrcE st hat, htgtE st hat⟩, fun _ _ _ he => by simp [o] at he⟩,
        fun c hc => ?_,
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
          · rw [if_neg (fun h0 => hbs' h0.2), GMap.lookup_delete_ne _ hbs', hat.ent _ hm1 b hb])
    hE hE' Φ $$ Hinv Hsi Hp [Hn] Hk
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hn
  iintro %w Hq Hp Hpost
  icases Hpost with (⟨%hW, -, Hl⟩ | ⟨%hW, %n, %x, -, Hlg, Hl, -⟩)
  · obtain ⟨e, rfl, he, -⟩ := hW
    icases osCallPerm_unchild R d bs _ j _ $$ Hp Hq with ⟨Hp, Hq⟩
    iapply HΦ $$ %e Hq Hp
    ileft
    isplitr
    · ipureintro; exact he rfl
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
  · obtain ⟨e, rfl, -, hR⟩ := hW
    icases osCallPerm_unchild R d bs _ j _ $$ Hp Hq with ⟨Hp, Hq⟩
    iapply HΦ $$ %e Hq Hp
    iright
    isplitr
    · ipureintro; exact hR rfl
    iexists x
    isplitl [Hlg]
    · iexact Hlg
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl

end specs

end Fs
end Perennial

end
