/-
The shared mode of the tree: the metadata steps that log an entry (`Unlink`, the file `Rename`s,
`Mkdir`, `Rmdir`, the directory `Rename`), over `wp_logStepS`. `TreeShared.lean` states the specs
and takes their proofs from here. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedLog
public import GooseLang.Ext.Fs.TreeSharedCallEnd

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

theorem restrictN_eq_of {N : NameSet} {e c : Ents} (h : ∀ b, N.Mem b → e !! b = c !! b) :
    restrictN N e = restrictN N c := by
  apply GMap.ext; intro b
  show restrictN N e !! b = restrictN N c !! b
  by_cases hb : N.Mem b
  · rw [restrictN_lookup _ _ _ hb, restrictN_lookup _ _ _ hb, h b hb]
  · rw [restrictN_lookup_not _ _ _ hb, restrictN_lookup_not _ _ _ hb]

theorem calls_start {st : OsState} {k s0 s' : Nat} (h1 : st.proc.calls !! k = some s0)
    (h2 : st.proc.calls !! k = some s') : s' = s0 := by
  rw [h1] at h2; exact (Option.some.inj h2).symm

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- What a spine says of the state. -/
theorem pathS_of (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) (st : OsState)
    (Γn : GMap (Ino × NameSet) NamesH) (hR : st.fs.roots = R)
    (hcoh : NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ osPathS (L := L) R d dq j -∗
      ⌜st.lookup d = some (.dir j)⌝ :=
  osPathS_lookup hR hcoh d dq j

theorem wp_osUnlinkS' (R : Roots) (d b : GoString) (j i : Ino) (dq : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hi : h.cur !! b = some (.file i)) (hs : h.next ≤ s0)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j (.only [b]) h ⟨.remove j b (.file i), s0⟩ (GMap.delete b h.cur)
          (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  have hbN' : ∀ b', (NameSet.only [b]).Mem b' → b' = b := by simp [NameSet.Mem]
  let o : MetaOp := .remove j b (.file i)
  let cl : List ClaimW := [(j, .only [b], h, restrictN (.only [b]) (GMap.delete b h.cur))]
  have hent : ∀ st, ClaimsAt st cl → st.tree.entry j b = some (.file i) := by
    intro st hat; rw [hat.ent _ (List.mem_singleton_self _) b hbN]; exact hi
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e' st' ∧ FilesSame st st' :=
    fun st _ _ hcall _ hp _ => ⟨_, st.metaEnd k, ⟨child d b, k, s0, rfl, treeName_child hp hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩, filesSame_metaEnd st k⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e' st' → ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧
          (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w true)) := by
    intro st e' st' hw _ hcall _ hp hat Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, hk', hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rw [calls_start hcall hk'] at hres
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    have hlt' : ∀ x, x ∈ o.apply st.tree → x < ((st.metaEnd k).metaDo o s0).fs.nextIno := by
      intro x hx
      rcases mem_remove _ _ _ _ _ hx with rfl | hx
      · exact hlt _ (mem_of_reach htw (reach_of_lookup hp))
      · exact hlt _ hx
    rcases hres with ⟨i', j0, b0, hfi, hpar, hr⟩ | ⟨e, he, rfl, rfl⟩
    · rw [parent_child hp hb] at hpar
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpar)
      rw [lookup_child hw.roots hp hb, hent st hat] at hfi
      cases Option.some.inj hfi
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, hlt', 0, rfl, by simp⟩⟩
      · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
      · exact ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, hlt', e, rfl, by simp⟩⟩
    · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
  have htree : ∀ st, FsTreeWf st → st.fs.roots = R → st.lookup d = some (.dir j) →
      ClaimsAt st cl →
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) := by
    intro st hw hR hp hat
    obtain ⟨htw, -, -⟩ := wf_tree hw
    have hjm : j ∈ st.tree := mem_of_reach htw (reach_of_lookup hp)
    refine ⟨hR ▸ treeWf_removeFile htw (reach_of_lookup hp) (hent st hat) _,
      named_remove _ _ _ _, fun x hx => ?_, fun J hJ => by simp [o, MetaOp.newDirs] at hJ,
      fun _ => ⟨⟨hjm, hent st hat⟩, fun _ _ _ he => by simp [o] at he⟩, fun c hc => ?_⟩
    · rcases mem_remove _ _ _ _ _ hx with rfl | hx
      · exact .inl hjm
      · exact .inl hx
    · rw [List.mem_singleton] at hc; subst hc
      apply restrictN_eq_of
      intro b' hb'
      obtain rfl := hbN' b' hb'
      rw [entsOf_lookup, entry_remove]; simp
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_logStepS "Unlink" _ (by simp [val.isPanic]) R k s0 q o cl
    (osPathS (L := L) R d dq j) (fun st => st.lookup d = some (.dir j))
    (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0))
    (by simp [cl]) (fun c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨b, hbN, .inl (by simp [o, MetaOp.slots])⟩)
    (by intro sl hsl; simp [o, MetaOp.slots] at hsl; subst hsl; exact ⟨_, List.mem_singleton_self _, rfl, hbN⟩)
    (by simp [cl, hs]) (by rintro ⟨J, hJ⟩; cases hJ) (by intro j b hb; simp [o, MetaOp.adds] at hb)
    (fun st Γn hR hcoh => pathS_of R d dq j st Γn hR hcoh) hprog hpost htree hE hE' Φ
    $$ Hinv Hsi Hp [Hn] Hk
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hn
  iintro %w Hq Hp Hpost
  icases Hpost with (⟨%hW, Hl⟩ | ⟨%hW, %x, Hlg, Hl, -⟩)
  · obtain ⟨e, rfl, he⟩ := hW
    iapply HΦ $$ %e Hq Hp
    unfold osNamesAfter
    ileft
    isplitr
    · ipureintro; exact he rfl
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
  · obtain ⟨e, rfl, -⟩ := hW
    iapply HΦ $$ %e Hq Hp
    unfold osNamesAfter
    iright
    iexists x
    isplitl [Hlg]
    · iexact Hlg
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl

/-- A rename's failing step, with no effect (the source no directory, or no other call). -/
theorem renameStep_err {st : OsState} {d bs d' bt : GoString} {j j' : Ino} {k s0 : Nat}
    (hd : st.lookup d = some (.dir j)) (hd' : st.lookup d' = some (.dir j')) (hbs : NameOk bs)
    (hbt : NameOk bt) (hcall : st.proc.calls !! k = some s0)
    (hex : (∃ J, st.lookup (child d bs) = some (.dir J)) →
      ∀ k' s', st.proc.calls !! k' = some s' → k' = k) :
    IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st
      (Val (#(1 : w64))) (st.metaEnd k) :=
  ⟨child d bs, child d' bt, k, s0, rfl, treeName_child hd hbs, treeName_child hd' hbt, hcall, hex,
    .inr (.inr ⟨1, by decide, rfl, rfl⟩)⟩

/-- A rename's step, the source the node `n`, the names distinct: an errno with no effect, or the
rename logged. -/
theorem renameStep_cases {st : OsState} {d bs d' bt : GoString} {j j' : Ino} {n : Node}
    {k s0 : Nat} {e' : Expr} {st' : OsState} (hw : FsTreeWf st)
    (hcall : st.proc.calls !! k = some s0)
    (hd : st.lookup d = some (.dir j)) (hd' : st.lookup d' = some (.dir j')) (hbs : NameOk bs)
    (hbt : NameOk bt) (hsrc : st.tree.entry j bs = some n) (hne : child d bs ≠ child d' bt)
    (Hst : IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st e' st') :
    ∃ e : w64, e' = Val (#e) ∧ ((st' = st.metaEnd k ∧ e ≠ 0) ∨
      st' = (st.metaEnd k).metaDo (.rename j bs j' bt n (st.tree.entry j' bt)) s0) := by
  simp only [IsFsStep] at Hst
  obtain ⟨s1, t1, k', start, hv, -, -, hk', -, hres⟩ := Hst
  obtain ⟨rfl, rfl, rfl⟩ := tokPair_inj hv
  rw [calls_start hcall hk'] at hres
  rcases hres with ⟨-, o, ho, hr⟩ | ⟨hst, -, -, -⟩ | ⟨e, he, rfl, rfl⟩
  · obtain ⟨js, bs', jt, bt', n', h1, h2, h3, rfl⟩ := ho
    rw [parent_child hd hbs] at h1; rw [parent_child hd' hbt] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
    rw [lookup_child hw.roots hd hbs, hsrc] at h3; cases h3
    rw [lookup_child hw.roots hd' hbt] at hr
    rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
    · exact ⟨0, rfl, .inr rfl⟩
    · exact ⟨e, rfl, .inl ⟨rfl, he⟩⟩
    · exact ⟨e, rfl, .inr rfl⟩
  · exact absurd hst hne
  · exact ⟨e, rfl, .inl ⟨rfl, he⟩⟩

/-- Two children of directories, equal: the same directory and name. -/
theorem child_eq {d bs d' bt : GoString} (hbs : NameOk bs) (hbt : NameOk bt)
    (h : child d bs = child d' bt) : d = d' ∧ bs = bt := by
  have h1 := congrArg parentOf h; rw [parentOf_child' _ _ hbs, parentOf_child' _ _ hbt] at h1
  have h2 := congrArg baseOf h; rw [baseOf_child' _ _ hbs, baseOf_child' _ _ hbt] at h2
  exact ⟨Option.some.inj h1, h2⟩

theorem wp_osRenameFileS' (R : Roots) (d bs d' bt : GoString) (j j' i : Ino) (N N' : NameSet)
    (dq dq' : DFrac) (h h' : NamesH) (k s0 : Nat) (q : Qp) (hbs : NameOk bs) (hbt : NameOk bt)
    (hN : N.Mem bs) (hN' : N'.Mem bt) (hkey : (j, N) ≠ (j', N'))
    (hsrc : h.cur !! bs = some (.file i)) (htgt : ∀ J, h'.cur !! bt ≠ some (.dir J))
    (hs : h.next ≤ s0) (hs' : h'.next ≤ s0) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osPathS (L := L) R d' dq' j' -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osNames (L := L) j' N' (DFrac.own 1) h' -∗
      osCallS (L := L) k s0 q -∗
      (∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osPathS (L := L) R d' dq' j' -∗
                ((⌜e ≠ 0⌝ ∗ osNames (L := L) j N (DFrac.own 1) h ∗ osNames (L := L) j' N' (DFrac.own 1) h') ∨
         ∃ x, osLogged (L := L) x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) ∗
           osNames (L := L) j N (DFrac.own 1) (h.log x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) (GMap.delete bs h.cur)) ∗
           osNames (L := L) j' N' (DFrac.own 1) (h'.log x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) (<[bt := .file i]> h'.cur))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d' bt)))))) @ s; E {{ Φ }} := by
  have hNe : N ≠ .only [] := fun h0 => by rw [h0] at hN; simp [NameSet.Mem] at hN
  have hN'e : N' ≠ .only [] := fun h0 => by rw [h0] at hN'; simp [NameSet.Mem] at hN'
  let o : MetaOp := .rename j bs j' bt (.file i) (h'.cur !! bt)
  let cl : List ClaimW := [(j, N, h, GMap.delete bs h.cur), (j', N', h', <[bt := .file i]> h'.cur)]
  let P : OsState → Prop := fun st => st.lookup d = some (.dir j) ∧ st.lookup d' = some (.dir j')
  have hcl : ∀ c, c ∈ cl ↔ c = (j, N, h, GMap.delete bs h.cur) ∨
      c = (j', N', h', <[bt := .file i]> h'.cur) := by
    intro c; simp [cl]
  have hm1 : (j, N, h, GMap.delete bs h.cur) ∈ cl := (hcl _).2 (.inl rfl)
  have hm2 : (j', N', h', <[bt := .file i]> h'.cur) ∈ cl := (hcl _).2 (.inr rfl)
  have hsrcE : ∀ st, ClaimsAt st cl → st.tree.entry j bs = some (.file i) := fun st hat => by
    rw [hat.ent _ hm1 bs hN]; exact hsrc
  have htgtE : ∀ st, ClaimsAt st cl → st.tree.entry j' bt = h'.cur !! bt := fun st hat =>
    hat.ent _ hm2 bt hN'
  have hdisj : ∀ st, ClaimsAt st cl → j = j' → ∀ b, N.Mem b → ¬ N'.Mem b :=
    fun st hat hj b hb hb' => hat.disj _ hm1 _ hm2 hj (fun hNN => hkey (by simp only at hNN; rw [hj, hNN])) b hb hb'
  have hneq : ∀ st, P st → ClaimsAt st cl → child d bs ≠ child d' bt := by
    intro st hp hat heq
    obtain ⟨rfl, rfl⟩ := child_eq hbs hbt heq
    have hjj : j = j' := by
      have := hp.1.symm.trans hp.2; simp at this; exact this
    exact hdisj st hat hjj bs hN hN'
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) → P st → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st
        e' st' ∧ FilesSame st st' := by
    intro st hw _ hcall _ hp hat
    refine ⟨_, _, renameStep_err hp.1 hp.2 hbs hbt hcall (fun ⟨J, hJ⟩ => ?_),
      filesSame_metaEnd st k⟩
    rw [lookup_child hw.roots hp.1 hbs, hsrcE st hat] at hJ; cases hJ
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) → P st → ClaimsAt st cl →
      IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st e' st' →
      ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧
          (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w true)) := by
    intro st e' st' hw _ hcall _ hp hat Hst
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    obtain ⟨e, rfl, hr⟩ := renameStep_cases hw hcall hp.1 hp.2 hbs hbt (hsrcE st hat)
      (hneq st hp hat) Hst
    rw [htgtE st hat] at hr
    rcases hr with ⟨rfl, he⟩ | rfl
    · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
    · refine ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, fun x hx => ?_, e, rfl, by simp⟩⟩
      rcases mem_rename _ _ _ _ _ _ _ _ hx with rfl | rfl | hx
      · exact hlt _ (mem_of_reach htw (reach_of_lookup hp.1))
      · exact hlt _ (mem_of_reach htw (reach_of_lookup hp.2))
      · exact hlt _ hx
  have htree : ∀ st, FsTreeWf st → st.fs.roots = R → P st → ClaimsAt st cl →
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) := by
    intro st hw hR hp hat
    obtain ⟨htw, -, -⟩ := wf_tree hw
    have hjm := mem_of_reach htw (reach_of_lookup hp.1)
    have hjm' := mem_of_reach htw (reach_of_lookup hp.2)
    have hnt : ∀ J, st.tree.entry j' bt ≠ some (.dir J) := fun J => by
      rw [htgtE st hat]; exact htgt J
    refine ⟨hR ▸ treeWf_renameFile htw (reach_of_lookup hp.1) (reach_of_lookup hp.2) hbt
        (hsrcE st hat) hnt _ _,
      named_rename _ _ _ _ _ _ _, fun x hx => ?_, fun J hJ => by simp [o, MetaOp.newDirs] at hJ,
      fun _ => ⟨⟨hjm, hjm', hsrcE st hat, htgtE st hat⟩, fun _ _ _ he => by simp [o] at he⟩,
      fun c hc => ?_⟩
    · rcases mem_rename _ _ _ _ _ _ _ _ hx with rfl | rfl | hx
      · exact .inl hjm
      · exact .inl hjm'
      · exact .inl hx
    · apply GMap.ext; intro b
      show restrictN c.2.1 (entsOf (o.apply st.tree) c.1) !! b = c.2.2.2 !! b
      have hap : ∀ b, (o.apply st.tree).entry j b = (if j' = j ∧ bt = b then some (.file i)
          else if j = j ∧ bs = b then none else st.tree.entry j b) := by
        intro b; rw [entry_rename, hsrcE st hat]
      have hap' : ∀ b, (o.apply st.tree).entry j' b = (if j' = j' ∧ bt = b then some (.file i)
          else if j = j' ∧ bs = b then none else st.tree.entry j' b) := by
        intro b; rw [entry_rename, hsrcE st hat]
      rcases (hcl c).1 hc with rfl | rfl
      · by_cases hb : N.Mem b
        · rw [restrictN_lookup _ _ _ hb, entsOf_lookup, hap]
          by_cases hbt' : j' = j ∧ bt = b
          · obtain ⟨rfl, rfl⟩ := hbt'; exact absurd hN' (hdisj st hat rfl bt hb)
          · rw [if_neg hbt']
            by_cases hbs' : bs = b
            · subst hbs'; simp
            · rw [if_neg (fun h0 => hbs' h0.2), GMap.lookup_delete_ne _ hbs', hat.ent _ hm1 b hb]
        · rw [restrictN_lookup_not _ _ _ hb]
          have hbs' : bs ≠ b := fun h0 => hb (h0 ▸ hN)
          rw [GMap.lookup_delete_ne _ hbs', hat.out _ hm1 b hb]
      · by_cases hb : N'.Mem b
        · rw [restrictN_lookup _ _ _ hb, entsOf_lookup, hap']
          by_cases hbt' : bt = b
          · subst hbt'; rw [if_pos ⟨rfl, rfl⟩, GMap.lookup_insert]
          · rw [if_neg (fun h0 => hbt' h0.2), GMap.lookup_insert_ne _ _ hbt']
            by_cases hbs' : j = j' ∧ bs = b
            · obtain ⟨hj, rfl⟩ := hbs'; exact absurd hb (hdisj st hat hj bs hN)
            · rw [if_neg hbs', hat.ent _ hm2 b hb]
        · rw [restrictN_lookup_not _ _ _ hb]
          have hbt' : bt ≠ b := fun h0 => hb (h0 ▸ hN')
          rw [GMap.lookup_insert_ne _ _ hbt', hat.out _ hm2 b hb]
  iintro #Hinv #Hsi Hp Hp' Hn Hn' Hk HΦ
  iapply wp_logStepS "Rename" _ (by simp [val.isPanic]) R k s0 q o cl
    iprop(osPathS (L := L) R d dq j ∗ osPathS (L := L) R d' dq' j') P
    (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0))
    (fun c hc => by
      rcases (hcl c).1 hc with rfl | rfl
      · exact hNe
      · exact hN'e)
    (fun c hc => by
      rcases (hcl c).1 hc with rfl | rfl
      · exact ⟨bs, hN, .inl (by simp [o, MetaOp.slots])⟩
      · exact ⟨bt, hN', .inl (by simp [o, MetaOp.slots])⟩)
    (fun sl hsl => by
      simp only [o, MetaOp.slots, List.mem_cons, List.mem_nil_iff, or_false] at hsl
      rcases hsl with rfl | rfl
      · exact ⟨_, hm1, rfl, hN⟩
      · exact ⟨_, hm2, rfl, hN'⟩)
    (fun c hc => by
      rcases (hcl c).1 hc with rfl | rfl
      · exact .inl hs
      · exact .inl hs')
    (fun hd => by
      simp only [o, MetaOp.IsDirOp] at hd
      rcases hd with ⟨J, hJ⟩ | ⟨J, hJ⟩
      · cases hJ
      · exact absurd hJ (htgt J))
    (fun j0 b hb => by
      simp only [o, MetaOp.adds] at hb
      split at hb
      · simp at hb; subst hb; exact hbt
      · simp at hb)
    (fun st Γn hR hcoh => by
      iintro HA ⟨Hp, Hp'⟩
      icases pathS_of R d dq j st Γn hR hcoh $$ HA Hp with %h1
      icases pathS_of R d' dq' j' st Γn hR hcoh $$ HA Hp' with %h2
      ipureintro; exact ⟨h1, h2⟩)
    hprog hpost htree hE hE' Φ $$ Hinv Hsi [Hp Hp'] [Hn Hn'] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hp'
  · iapply (BigSepL.bigSepL_cons).2
    isplitl [Hn]
    · iexact Hn
    · iapply (BigSepL.bigSepL_singleton).2; iexact Hn'
  iintro %w Hq ⟨Hp, Hp'⟩ Hpost
  icases Hpost with (⟨%hW, Hl⟩ | ⟨%hW, %x, Hlg, Hl, -⟩)
  · obtain ⟨e, rfl, he⟩ := hW
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨Hn, Hl⟩
    icases (BigSepL.bigSepL_singleton).1 $$ Hl with Hn'
    iapply HΦ $$ %e Hq Hp Hp'
    ileft
    isplitr
    · ipureintro; exact he rfl
    isplitl [Hn]
    · iexact Hn
    · iexact Hn'
  · obtain ⟨e, rfl, -⟩ := hW
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨Hn, Hl⟩
    icases (BigSepL.bigSepL_singleton).1 $$ Hl with Hn'
    iapply HΦ $$ %e Hq Hp Hp'
    iright
    iexists x
    isplitl [Hlg]
    · iexact Hlg
    isplitl [Hn]
    · iexact Hn
    · iexact Hn'

/-- **A rename within one claim** of `d/bs` (the node `n`) to `d/bt` (holding `old`): the generic
step of `wp_osRenameFileS1` and `wp_osRenameDirS`. -/
theorem wp_osRename1S (R : Roots) (d bs bt : GoString) (j : Ino) (N : NameSet) (n : Node)
    (old : Option Node) (dq : DFrac) (h : NamesH) (k s0 : Nat) (q : Qp) (hbs : NameOk bs)
    (hbt : NameOk bt) (hN : N.Mem bs) (hN' : N.Mem bt) (hne : bs ≠ bt)
    (hsrc : h.cur !! bs = some n) (hold : h.cur !! bt = old)
    (hs : h.next ≤ s0 ∨ q = 1) (hdir : (MetaOp.rename j bs j bt n old).IsDirOp → q = 1)
    (hdirn : (∃ J, n = .dir J) → q = 1)
    (hwf : ∀ st, FsTreeWf st → st.lookup d = some (.dir j) → st.tree.entry j bs = some n →
      st.tree.entry j bt = old → TreeWf st.fs.roots ((MetaOp.rename j bs j bt n old).apply st.tree))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j N h ⟨.rename j bs j bt n old, s0⟩
          (<[bt := n]> (GMap.delete bs h.cur)) (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} := by
  have hNe : N ≠ .only [] := fun h0 => by rw [h0] at hN; simp [NameSet.Mem] at hN
  let o : MetaOp := .rename j bs j bt n old
  let cl : List ClaimW := [(j, N, h, restrictN N (<[bt := n]> (GMap.delete bs h.cur)))]
  have hm1 : (j, N, h, restrictN N (<[bt := n]> (GMap.delete bs h.cur))) ∈ cl :=
    List.mem_singleton_self _
  have hsrcE : ∀ st, ClaimsAt st cl → st.tree.entry j bs = some n := fun st hat => by
    rw [hat.ent _ hm1 bs hN]; exact hsrc
  have htgtE : ∀ st, ClaimsAt st cl → st.tree.entry j bt = old := fun st hat => by
    rw [hat.ent _ hm1 bt hN']; exact hold
  have hneq : child d bs ≠ child d bt := fun heq => hne (child_eq hbs hbt heq).2
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))) st
        e' st' ∧ FilesSame st st' := by
    intro st hw _ hcall hsole hp hat
    refine ⟨_, _, renameStep_err hp hp hbs hbt hcall (fun ⟨J, hJ⟩ => hsole (hdirn ⟨J, ?_⟩)),
      filesSame_metaEnd st k⟩
    rw [lookup_child hw.roots hp hbs, hsrcE st hat] at hJ; exact Option.some.inj hJ
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))) st e' st' →
      ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧
          (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w true)) := by
    intro st e' st' hw _ hcall _ hp hat Hst
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    obtain ⟨e, rfl, hr⟩ := renameStep_cases hw hcall hp hp hbs hbt (hsrcE st hat) hneq Hst
    rw [htgtE st hat] at hr
    rcases hr with ⟨rfl, he⟩ | rfl
    · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
    · refine ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, fun x hx => ?_, e, rfl, by simp⟩⟩
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
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) := by
    intro st hw hR hp hat
    obtain ⟨htw, -, -⟩ := wf_tree hw
    have hjm := mem_of_reach htw (reach_of_lookup hp)
    refine ⟨hR ▸ hwf st hw hp (hsrcE st hat) (htgtE st hat),
      named_rename _ _ _ _ _ _ _, fun x hx => ?_, fun J hJ => by simp [o, MetaOp.newDirs] at hJ,
      fun _ => ⟨⟨hjm, hjm, hsrcE st hat, htgtE st hat⟩, fun _ _ _ he => by simp [o] at he⟩,
      fun c hc => ?_⟩
    · rcases mem_rename _ _ _ _ _ _ _ _ hx with rfl | rfl | hx
      · exact .inl hjm
      · exact .inl hjm
      · exact .inl hx
    · rw [List.mem_singleton] at hc; subst hc
      apply restrictN_eq_of
      intro b hb
      rw [entsOf_lookup, entry_rename, hsrcE st hat]
      show (if j = j ∧ bt = b then some n else if j = j ∧ bs = b then none else st.tree.entry j b) = _
      by_cases hbt' : bt = b
      · subst hbt'; rw [if_pos ⟨rfl, rfl⟩, GMap.lookup_insert]
      · rw [if_neg (fun h0 => hbt' h0.2), GMap.lookup_insert_ne _ _ hbt']
        by_cases hbs' : bs = b
        · subst hbs'; simp
        · rw [if_neg (fun h0 => hbs' h0.2), GMap.lookup_delete_ne _ hbs', hat.ent _ hm1 b hb]
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_logStepS "Rename" _ (by simp [val.isPanic]) R k s0 q o cl
    (osPathS (L := L) R d dq j) (fun st => st.lookup d = some (.dir j))
    (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0))
    (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact hNe)
    (fun c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨bs, hN, .inl (by simp [o, MetaOp.slots])⟩)
    (fun sl hsl => by
      simp only [o, MetaOp.slots, List.mem_cons, List.mem_nil_iff, or_false] at hsl
      rcases hsl with rfl | rfl
      · exact ⟨_, hm1, rfl, hN⟩
      · exact ⟨_, hm1, rfl, hN'⟩)
    (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact hs) hdir
    (fun j0 b hb => by
      simp only [o, MetaOp.adds] at hb
      split at hb
      · simp at hb; subst hb; exact hbt
      · simp at hb)
    (fun st Γn hR hcoh => pathS_of R d dq j st Γn hR hcoh) hprog hpost htree hE hE' Φ
    $$ Hinv Hsi Hp [Hn] Hk
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hn
  iintro %w Hq Hp Hpost
  icases Hpost with (⟨%hW, Hl⟩ | ⟨%hW, %x, Hlg, Hl, -⟩)
  · obtain ⟨e, rfl, he⟩ := hW
    iapply HΦ $$ %e Hq Hp
    unfold osNamesAfter
    ileft
    isplitr
    · ipureintro; exact he rfl
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
  · obtain ⟨e, rfl, -⟩ := hW
    iapply HΦ $$ %e Hq Hp
    unfold osNamesAfter
    iright
    iexists x
    isplitl [Hlg]
    · iexact Hlg
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl

theorem wp_osRenameFileS1' (R : Roots) (d bs bt : GoString) (j i : Ino) (N : NameSet)
    (dq : DFrac) (h : NamesH) (k s0 : Nat) (q : Qp) (hbs : NameOk bs) (hbt : NameOk bt)
    (hN : N.Mem bs) (hN' : N.Mem bt) (hne : bs ≠ bt)
    (hsrc : h.cur !! bs = some (.file i)) (htgt : ∀ J, h.cur !! bt ≠ some (.dir J))
    (hs : h.next ≤ s0) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j N h ⟨.rename j bs j bt (.file i) (h.cur !! bt), s0⟩
          (<[bt := .file i]> (GMap.delete bs h.cur)) (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} :=
  wp_osRename1S R d bs bt j N (.file i) (h.cur !! bt) dq h k s0 q hbs hbt hN hN' hne hsrc rfl
    (.inl hs)
    (fun hd => by
      simp only [MetaOp.IsDirOp] at hd
      rcases hd with ⟨J, hJ⟩ | ⟨J, hJ⟩
      · cases hJ
      · exact absurd hJ (htgt J))
    (fun ⟨J, hJ⟩ => by cases hJ)
    (fun st hw hp hent htg => by
      obtain ⟨htw, -, -⟩ := wf_tree hw
      exact treeWf_renameFile htw (reach_of_lookup hp) (reach_of_lookup hp) hbt hent
        (fun J => by rw [htg]; exact htgt J) _ _)
    hE hE' Φ

theorem wp_osRenameDirS' (R : Roots) (d bs bt : GoString) (j J : Ino) (N : NameSet) (dq : DFrac)
    (h : NamesH) (k s0 : Nat) (hbs : NameOk bs) (hbt : NameOk bt) (hN : N.Mem bs) (hN' : N.Mem bt)
    (hne : bs ≠ bt) (hsrc : h.cur !! bs = some (.dir J)) (htgt : h.cur !! bt = none)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osCallS (L := L) k s0 1 -∗
      (∀ e : w64, osCallPerm (L := L) 1 -∗ osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j N h ⟨.rename j bs j bt (.dir J) none, s0⟩
          (<[bt := .dir J]> (GMap.delete bs h.cur)) (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} :=
  wp_osRename1S R d bs bt j N (.dir J) none dq h k s0 1 hbs hbt hN hN' hne hsrc htgt (.inr rfl)
    (fun _ => rfl) (fun _ => rfl)
    (fun st hw hp hent htg => by
      obtain ⟨htw, -, -⟩ := wf_tree hw
      have hss : st.lookup (child d bs) = some (.dir J) := by
        rw [lookup_child hw.roots hp hbs]; exact hent
      have hnot : ¬ BelowP st.tree J j := fun hb =>
        not_isUnder_child_self d bs (isUnder_of_belowP hw.roots htw hss hp hb)
      exact treeWf_renameDir htw (reach_of_lookup hp) (reach_of_lookup hp) hbt hent
        (fun h0 => hne h0.2) (.inl htg) hnot _ _)
    hE hE' Φ

theorem wp_osRmdirS' (R : Roots) (d b : GoString) (j J : Ino) (dq : DFrac) (h hJ : NamesH)
    (k s0 : Nat) (hb : NameOk b) (hd : h.cur !! b = some (.dir J)) (he : hJ.cur = ∅)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗
      osNames (L := L) J (.except []) (DFrac.own 1) hJ -∗ osCallS (L := L) k s0 1 -∗
      (∀ e : w64, osCallPerm (L := L) 1 -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) J (.except []) (DFrac.own 1) hJ -∗
        osNamesAfter (L := L) j (.only [b]) h ⟨.remove j b (.dir J), s0⟩ (GMap.delete b h.cur)
          (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  have hbN' : ∀ b', (NameSet.only [b]).Mem b' → b' = b := by simp [NameSet.Mem]
  let o : MetaOp := .remove j b (.dir J)
  let cl : List ClaimW := [(j, .only [b], h, restrictN (.only [b]) (GMap.delete b h.cur))]
  let P : OsState → Prop := fun st => st.lookup d = some (.dir j) ∧ ∀ c, st.tree.entry J c = none
  have hent : ∀ st, ClaimsAt st cl → st.tree.entry j b = some (.dir J) := by
    intro st hat; rw [hat.ent _ (List.mem_singleton_self _) b hbN]; exact hd
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      ((1 : Qp) = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) → P st → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' st' ∧ FilesSame st st' :=
    fun st _ _ hcall _ hp _ => ⟨_, st.metaEnd k, ⟨child d b, k, s0, rfl, treeName_child hp.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩, filesSame_metaEnd st k⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      ((1 : Qp) = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) → P st → ClaimsAt st cl →
      IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' st' → ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧
          (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w true)) := by
    intro st e' st' hw _ hcall _ hp hat Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, hk', hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rw [calls_start hcall hk'] at hres
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    have hlt' : ∀ x, x ∈ o.apply st.tree → x < ((st.metaEnd k).metaDo o s0).fs.nextIno := by
      intro x hx
      rcases mem_remove _ _ _ _ _ hx with rfl | hx
      · exact hlt _ (mem_of_reach htw (reach_of_lookup hp.1))
      · exact hlt _ hx
    rcases hres with ⟨J', j0, b0, ⟨hJ', -⟩, hpar, hr⟩ | ⟨e, he, rfl, rfl⟩
    · rw [parent_child hp.1 hb] at hpar
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpar)
      rw [lookup_child hw.roots hp.1 hb, hent st hat] at hJ'
      cases Option.some.inj hJ'
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, hlt', 0, rfl, by simp⟩⟩
      · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
      · exact ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, hlt', e, rfl, by simp⟩⟩
    · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
  have htree : ∀ st, FsTreeWf st → st.fs.roots = R → P st → ClaimsAt st cl →
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) := by
    intro st hw hR hp hat
    obtain ⟨htw, -, -⟩ := wf_tree hw
    have hjm : j ∈ st.tree := mem_of_reach htw (reach_of_lookup hp.1)
    refine ⟨hR ▸ treeWf_rmdir htw (reach_of_lookup hp.1) (hent st hat) hp.2 _,
      named_remove _ _ _ _, fun x hx => ?_, fun J hJ => by simp [o, MetaOp.newDirs] at hJ,
      fun hnd => absurd ⟨J, rfl⟩ hnd, fun c hc => ?_⟩
    · rcases mem_remove _ _ _ _ _ hx with rfl | hx
      · exact .inl hjm
      · exact .inl hx
    · rw [List.mem_singleton] at hc; subst hc
      apply restrictN_eq_of
      intro b' hb'
      obtain rfl := hbN' b' hb'
      rw [entsOf_lookup, entry_remove]; simp
  iintro #Hinv #Hsi Hp Hn HJ Hk HΦ
  iapply wp_logStepS "Rmdir" _ (by simp [val.isPanic]) R k s0 1 o cl
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) J (.except []) (DFrac.own 1) hJ) P
    (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0))
    (by simp [cl])
    (fun c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨b, hbN, .inl (by simp [o, MetaOp.slots])⟩)
    (by intro sl hsl; simp [o, MetaOp.slots] at hsl; subst hsl
        exact ⟨_, List.mem_singleton_self _, rfl, hbN⟩)
    (fun _ _ => .inr rfl) (fun _ => rfl) (by intro j b hb; simp [o, MetaOp.adds] at hb)
    (fun st Γn hR hcoh => by
      iintro HA ⟨Hp, HJ⟩
      icases pathS_of R d dq j st Γn hR hcoh $$ HA Hp with %h1
      icases osNames_entry hcoh J (.except []) _ hJ $$ HA HJ with %h2
      ipureintro
      refine ⟨h1, fun c => ?_⟩
      rw [h2 c (by simp [NameSet.Mem]), he]; rfl)
    hprog hpost htree hE hE' Φ
    $$ Hinv Hsi [Hp HJ] [Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact HJ
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hn
  iintro %w Hq ⟨Hp, HJ⟩ Hpost
  icases Hpost with (⟨%hW, Hl⟩ | ⟨%hW, %x, Hlg, Hl, -⟩)
  · obtain ⟨e, rfl, he⟩ := hW
    iapply HΦ $$ %e Hq Hp HJ
    unfold osNamesAfter
    ileft
    isplitr
    · ipureintro; exact he rfl
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
  · obtain ⟨e, rfl, -⟩ := hW
    iapply HΦ $$ %e Hq Hp HJ
    unfold osNamesAfter
    iright
    iexists x
    isplitl [Hlg]
    · iexact Hlg
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl

/-- **`mkdir(2)`** of the free name `d/b` (shared mode), by a call holding the whole permission. -/
theorem wp_osMkdirS' (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH) (k s0 : Nat)
    (hb : NameOk b) (hn : h.cur !! b = none) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 1 -∗
      (∀ e : w64, osCallPerm (L := L) 1 -∗ osPathS (L := L) R d dq j -∗
        ((⌜e ≠ 0⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h) ∨
         ∃ x J, osLogged (L := L) x (⟨.mkdir j b J, s0⟩ : LogEntry) ∗
           osNames (L := L) j (.only [b]) (DFrac.own 1) (h.log x (⟨.mkdir j b J, s0⟩ : LogEntry) (<[b := .dir J]> h.cur)) ∗
           ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗ ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Mkdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  have hbN' : ∀ b', (NameSet.only [b]).Mem b' → b' = b := by simp [NameSet.Mem]
  let oF : Nat → MetaOp := fun n => .mkdir j b n
  let cl : List ClaimW := [(j, .only [b], h, ∅)]
  let curF : Nat → ClaimW → Ents := fun n _ => <[b := .dir n]> h.cur
  let W : val → Bool → Prop := fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)
  have hent : ∀ st, ClaimsAt st cl → st.tree.entry j b = none := by
    intro st hat; rw [hat.ent _ (List.mem_singleton_self _) b hbN]; exact hn
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      ((1 : Qp) = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Mkdir" (PairV (osTokV k) (#(child d b))) st e' st' ∧ FilesSame st st' :=
    fun st _ _ hcall _ hp _ => ⟨_, st.metaEnd k, ⟨child d b, k, s0, rfl, treeName_child hp hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩, filesSame_metaEnd st k⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      ((1 : Qp) = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Mkdir" (PairV (osTokV k) (#(child d b))) st e' st' → ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ W w false) ∨
         (LoggedFrom st st' k s0 (oF st.fs.nextIno) ∧
          (∀ x, x ∈ (oF st.fs.nextIno).apply st.tree → x < st'.fs.nextIno) ∧ W w true)) := by
    intro st e' st' hw _ hcall _ hp hat Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, hk', hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rw [calls_start hcall hk'] at hres
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    have hlt' : ∀ x, x ∈ (oF st.fs.nextIno).apply st.tree →
        x < ((st.metaEnd k).takeIno.metaDo (oF st.fs.nextIno) s0).fs.nextIno := by
      intro x hx
      rcases mem_mkdir _ _ _ _ _ hx with rfl | rfl | hx
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hlt _ (mem_of_reach htw (reach_of_lookup hp)))
      · exact Nat.lt_succ_of_lt (hlt _ hx)
    rcases hres with ⟨j0, b0, -, hpar, hr⟩ | ⟨e, he, rfl, rfl⟩
    · rw [parent_child hp hb] at hpar
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpar)
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨_, rfl, .inr ⟨loggedFrom_metaDoIno st k s0 _, hlt', 0, rfl, by simp⟩⟩
      · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
      · exact ⟨_, rfl, .inr ⟨loggedFrom_metaDoIno st k s0 _, hlt', e, rfl, by simp⟩⟩
    · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
  have htree : ∀ st, FsTreeWf st → st.fs.roots = R → st.lookup d = some (.dir j) →
      ClaimsAt st cl →
      let o := oF st.fs.nextIno
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = curF st.fs.nextIno c) := by
    intro st hw hR hp hat
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    have hjm : j ∈ st.tree := mem_of_reach htw (reach_of_lookup hp)
    have hJm : st.fs.nextIno ∉ st.tree := fun h => Nat.lt_irrefl _ (hlt _ h)
    have hJr : ∀ r, (r, st.fs.nextIno) ∉ st.fs.roots := fun r h =>
      hJm (mem_of_reach htw (.root r _ h))
    have hJj : st.fs.nextIno ≠ j := fun h => hJm (h ▸ hjm)
    refine ⟨hR ▸ treeWf_mkdir htw (reach_of_lookup hp) hb (hent st hat) hJm hJr,
      named_mkdir _ _ _ _, fun x hx => ?_, fun J hJ => ?_, fun hnd => absurd trivial hnd,
      fun c hc => ?_⟩
    · rcases mem_mkdir _ _ _ _ _ hx with rfl | rfl | hx
      · exact .inr (by simp [oF, MetaOp.newDirs])
      · exact .inl hjm
      · exact .inl hx
    · simp only [oF, MetaOp.newDirs, List.mem_singleton] at hJ
      subst hJ; exact hJm
    · rw [List.mem_singleton] at hc; subst hc
      apply GMap.ext; intro b'
      show restrictN (.only [b]) (entsOf _ j) !! b' = (<[b := .dir st.fs.nextIno]> h.cur) !! b'
      by_cases hb' : (NameSet.only [b]).Mem b'
      · obtain rfl := hbN' b' hb'
        rw [restrictN_lookup _ _ _ hb', entsOf_lookup, entry_mkdir, if_neg hJj, if_pos ⟨rfl, rfl⟩,
          GMap.lookup_insert]
      · rw [restrictN_lookup_not _ _ _ hb']
        have hne : b ≠ b' := fun h => hb' (h ▸ hbN)
        rw [GMap.lookup_insert_ne _ _ hne]
        exact (hat.out _ (List.mem_singleton_self _) b' hb').symm
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_logStepSN "Mkdir" _ (by simp [val.isPanic]) R k s0 1 oF cl curF
    (osPathS (L := L) R d dq j) (fun st => st.lookup d = some (.dir j)) W
    (by simp [cl]) (fun _ c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨b, hbN, .inl (by simp [oF, MetaOp.slots])⟩)
    (by intro n sl hsl; simp [oF, MetaOp.slots] at hsl; subst hsl
        exact ⟨_, List.mem_singleton_self _, rfl, hbN⟩)
    (fun _ _ => .inr rfl) (fun _ _ => rfl)
    (by intro n j' b' hb'; simp [oF, MetaOp.adds] at hb'; rw [hb'.2]; exact hb)
    (fun st Γn hR hcoh => pathS_of R d dq j st Γn hR hcoh) hprog hpost htree hE hE' Φ
    $$ Hinv Hsi Hp [Hn] Hk
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hn
  iintro %w Hq Hp Hpost
  icases Hpost with (⟨%hW, Hl⟩ | ⟨%hW, %n, %x, Hlg, Hl, HJ⟩)
  · obtain ⟨e, rfl, he⟩ := hW
    iapply HΦ $$ %e Hq Hp
    ileft
    isplitr
    · ipureintro; exact he rfl
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
  · obtain ⟨e, rfl, -⟩ := hW
    iapply HΦ $$ %e Hq Hp
    iright
    iexists x, n
    isplitl [Hlg]
    · iexact Hlg
    isplitl [Hl]
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
    · rw [show (oF n).newDirs = [n] from rfl]
      iapply (BigSepL.bigSepL_singleton).1 $$ HJ

end specs

end Fs
end Perennial

end
