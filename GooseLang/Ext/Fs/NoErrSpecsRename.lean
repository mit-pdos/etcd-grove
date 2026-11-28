/-
What the program logic may use of the premise **no I/O error** (`NoIoErr`) on `rename(2)` of a
covered path in the shared mode (S5, 2026-11-18, `notes/bbolt-integration-plan.md`): a file `d/bs`
renamed onto `d'/bt`, a file or nothing, the two names in two claims held whole, has a success
(`renameFile_succ`: the source a file, the target no directory), so under `NoIoErr` its step returns
errno 0 and logs the rename (`wp_osRenameFileSNE`). Over `wp_logStepSQ`, `wp_logStepS` whose `hpost`
also gets the semantics' own step (`wp_logStepSWQ`'s, as `wp_osOpenCreateSQ` uses it). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedMeta
public import GooseLang.Ext.Fs.NoIoErrSpecs

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section step
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] [S : ExtSemantics fsExt] [FsSemOk]

/-- **`rename(2)` of the file `d/bs` onto `d'/bt`, no directory, has a success**: the source a
file, the names distinct. -/
theorem renameFile_succ {st : OsState} {d bs d' bt : GoString} {j j' i : Ino} {k s0 : Nat}
    (hw : FsTreeWf st) (hcall : st.proc.calls !! k = some (s0, child d bs))
    (hsr : st.SameRoot (child d bs) (child d' bt))
    (hd : st.lookup d = some (.dir j)) (hd' : st.lookup d' = some (.dir j')) (hbs : NameOk bs)
    (hbt : NameOk bt) (hsrc : st.tree.entry j bs = some (.file i)) (hne : child d bs ≠ child d' bt)
    (htgt : ∀ J, st.tree.entry j' bt ≠ some (.dir J)) :
    ∃ st'', IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st
      (Val (#(0 : w64))) st'' := by
  have hls : st.lookup (child d bs) = some (.file i) := by
    rw [lookup_child hw.roots hd hbs, hsrc]
  have hlt : st.lookup (child d' bt) = st.tree.entry j' bt := lookup_child hw.roots hd' hbt
  have hex : (∃ J, st.lookup (child d bs) = some (.dir J)) →
      ∀ k' s' p', st.proc.calls !! k' = some (s', p') → k' = k ∨ ¬ st.SameRoot (child d bs) p' := by
    rintro ⟨J, hJ⟩; rw [hls] at hJ; cases hJ
  have hok : RenameOk st (child d bs) (child d' bt) := by
    refine ⟨hne, ⟨_, parent_child hd hbs⟩, ⟨_, parent_child hd' hbt⟩, ?_⟩
    rw [hls]
    intro J hJ
    rw [hlt] at hJ
    exact htgt J hJ
  have hop : RenameOp st (child d bs) (child d' bt)
      (.rename j bs j' bt (.file i) (st.lookup (child d' bt))) :=
    ⟨j, bs, j', bt, .file i, parent_child hd hbs, parent_child hd' hbt, hls, rfl⟩
  exact ⟨_, child d bs, child d' bt, k, s0, rfl, treeName_child hd hbs, treeName_child hd' hbt,
    hsr, hcall, hex, .inl ⟨hok, _, hop, .inl ⟨rfl, rfl⟩⟩⟩

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`wp_logStepS` whose `hpost` also gets the semantics' own step** (from `wp_logStepSWQ`, as
`wp_logStepSN` is from `wp_logStepSW`). -/
theorem wp_logStepSQ (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat) (pc : GoString)
    (q : Qp) (o : MetaOp) (cl : List ClaimW) (F : IProp GF) (P : OsState → Prop)
    (W : val → Bool → Prop)
    (hne : ∀ c ∈ cl, c.2.1 ≠ .only [])
    (hwr : ∀ c ∈ cl, ∃ b, c.2.1.Mem b ∧ o.Writes c.1 b)
    (hslots : ∀ sl ∈ o.slots, ∃ c ∈ cl, c.1 = sl.1 ∧ c.2.1.Mem sl.2)
    (hnext : ∀ c ∈ cl, c.2.2.1.next ≤ s0 ∨ q = 1)
    (hdir : o.IsDirOp → q = 1)
    (hadd : ∀ j b, b ∈ o.adds j → NameOk b)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' →
      (∃ hh hh', ExtSemantics.step (E := fsExt) GoLocalContext.typeFns op v hh st () e' hh' st' ()) →
      ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ W w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧ W w true)))
    (hfs : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, pc) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R pc → k' = k) → P st →
      ClaimsAt st cl → IsFsStep op v st e' st' → FilesSame st st')
    (htree : ∀ st, FsTreeWf st → st.fs.roots = R → P st → ClaimsAt st cl →
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) ∧
      (∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF)
    (hO : op ≠ "OutClose" := by decide) (hl : ¬ LockOp op := by simp [LockOp])
    (hM : op ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗
      ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) -∗
      osCallS (L := L) k s0 pc q -∗
      (∀ w, osCallPerm (L := L) (callKey R pc) q -∗ F -∗
        ((⌜W w false⌝ ∗ [∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1) c.2.2.1) ∨
         (⌜W w true⌝ ∗ ∃ x, osLogged (L := L) x ⟨o, s0⟩ ∗
           ([∗list] c ∈ cl, osNames (L := L) c.1 c.2.1 (DFrac.own 1)
             (c.2.2.1.log x ⟨o, s0⟩ c.2.2.2)) ∗
           [∗list] J ∈ o.newDirs, ∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ ∗
             ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)) -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hcl Hk HΦ
  iapply wp_logStepSWQ op v hv R k s0 pc q (fun _ => o) cl (fun _ c => c.2.2.2) F P W
    (fun _ _ _ => emp) hne (fun _ => hwr) (fun _ => hslots) hnext (fun _ => hdir) (fun _ => hadd)
    hF hprog
    (fun st e' st' hw hR hcall hsole hP hat Hst Hsem => by
      obtain ⟨w, rfl, hres⟩ := hpost st e' st' hw hR hcall hsole hP hat Hst Hsem
      rcases hres with ⟨rfl, hW⟩ | ⟨hlf, hlt, hW⟩
      · exact ⟨w, rfl, fsTreeWf_metaEnd hw k, .inl ⟨endedT_metaEnd st k, hW⟩⟩
      · obtain ⟨htw, hnm, -⟩ := htree st hw hR hP hat
        exact ⟨w, rfl, hlf.wf hw (hR ▸ htw) hnm hlt, .inr ⟨hlf.toT, hW⟩⟩)
    (fun st e' st' h h' Γb Γm Γf Γt w lg hw hR hcall hsole hP hat Hst hew hW hend hlog Hr Hfr => by
      have hs : FilesSame st st' := hfs st e' st' hw hR hcall hsole hP hat Hst
      iintro Hw
      imod osWorld_filesSame hs Hr Hfr $$ Hw with Hw
      imodintro
      iexists Γb, Γm, Γf, Γt
      iframe)
    (fun st _ _ hw hR _ hP hat _ _ => by
      obtain ⟨-, -, h3⟩ := htree st hw hR hP hat
      exact h3)
    hE hE' Φ hO hl hM $$ Hinv Hsi HF Hcl Hk
  iintro %w Hq HF Hp
  iapply HΦ $$ %w Hq HF
  icases Hp with (⟨%hW, -, Hp⟩ | ⟨%hW, %n, %x, -, Hp⟩)
  · ileft; isplitr
    · ipureintro; exact hW
    · iexact Hp
  · iright
    isplitr
    · ipureintro; exact hW
    · iexists x; iexact Hp

/-- **`rename(2)` of the file `d/bs` (inode `i`) onto `d'/bt` (a file or nothing) with no error**
(shared mode, the two claims whole, of distinct keys, the paths of one root; `wp_osRenameFileS'`
under `NoIoErr`, the paths covered): the rename logged, errno 0. -/
theorem wp_osRenameFileSNE (Sio : IoSet) [FsStepSat (NoIoErr Sio)] (R : Roots) (d bs d' bt : GoString) (j j' i : Ino)
    (N N' : NameSet) (dq dq' : DFrac) (h h' : NamesH) (k s0 : Nat) (q : Qp) (hbs : NameOk bs)
    (hbt : NameOk bt) (hN : N.Mem bs) (hN' : N'.Mem bt) (hkey : (j, N) ≠ (j', N'))
    (hsrc : h.cur !! bs = some (.file i)) (htgt : ∀ J, h'.cur !! bt ≠ some (.dir J))
    (hs : h.next ≤ s0) (hs' : h'.next ≤ s0) (hsr : SameRootR R (child d bs) (child d' bt))
    (hS : Sio.path (child d bs) ∨ Sio.path (child d' bt))
    (hfit : PathFits (child d bs) ∧ PathFits (child d' bt)) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osPathS (L := L) R d' dq' j' -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osNames (L := L) j' N' (DFrac.own 1) h' -∗
      osCallS (L := L) k s0 (child d bs) q -∗
      (osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗ osPathS (L := L) R d' dq' j' -∗
        (∃ x, osLogged (L := L) x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) ∗
           osNames (L := L) j N (DFrac.own 1) (h.log x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) (GMap.delete bs h.cur)) ∗
           osNames (L := L) j' N' (DFrac.own 1) (h'.log x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) (<[bt := .file i]> h'.cur))) -∗
        Φ (#(0 : w64))) -∗
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
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, child d bs) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R (child d bs) → k' = k) →
      P st → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st
        e' st' ∧ FilesSame st st' := by
    intro st hw hR hcall _ hp hat
    refine ⟨_, _, renameStep_err hp.1 hp.2 hbs hbt (sameRoot_of_R hR hsr) hcall (fun ⟨J, hJ⟩ => ?_),
      filesSame_metaEnd st k⟩
    rw [lookup_child hw.roots hp.1 hbs, hsrcE st hat] at hJ; cases hJ
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, child d bs) →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → callKey R s'.2 = callKey R (child d bs) → k' = k) →
      P st → ClaimsAt st cl →
      IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st e' st' →
      (∃ hh hh', ExtSemantics.step (E := fsExt) GoLocalContext.typeFns "Rename"
        (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) hh st () e' hh' st' ()) →
      ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ (fun w lg => w = #(0 : w64) ∧ lg = true) w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧
          (fun w lg => w = #(0 : w64) ∧ lg = true) w true)) := by
    intro st e' st' hw hR hcall _ hp hat Hst Hsem
    obtain ⟨hh, hh', Hsem⟩ := Hsem
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    -- the premise: a success exists, so the step has errno 0
    have hz : e' = Val (#(0 : w64)) := by
      obtain ⟨st'', hst''⟩ := renameFile_succ hw hcall (sameRoot_of_R hR hsr) hp.1 hp.2 hbs hbt (hsrcE st hat)
        (hneq st hp hat) (fun J hJ => htgt J (by rw [← htgtE st hat]; exact hJ))
      have := noIoErr_step (Sio := Sio) Hsem
        (by simp only [IoCovers]; exact ⟨k, child d bs, child d' bt, rfl, hS, hfit.1, hfit.2⟩)
        ⟨_, st'', hst'', rfl⟩
      exact this
    obtain ⟨e, rfl, hr⟩ := renameStep_cases hw hcall hp.1 hp.2 hbs hbt (hsrcE st hat)
      (hneq st hp hat) Hst
    have he0 : e = 0 := by
      have := congrArg (fun x : Expr => x) hz
      injection hz with hz'
      exact go.intoVal_inj hz'
    subst he0
    rw [htgtE st hat] at hr
    rcases hr with ⟨rfl, he⟩ | rfl
    · exact absurd rfl he
    · refine ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, fun x hx => ?_, rfl, rfl⟩⟩
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
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) ∧
      (∃ rj ∈ R, IsUnder rj.1 (child d bs) ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2 c.1) := by
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
      fun c hc => ?_,
      rootClause_two hw.roots hR hp.1 hp.2 hsr (by intro c hc; rcases (hcl c).1 hc with rfl | rfl <;> simp)⟩
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
  iapply wp_logStepSQ "Rename" _ (by simp [val.isPanic]) R k s0 (child d bs) q o cl
    iprop(osPathS (L := L) R d dq j ∗ osPathS (L := L) R d' dq' j') P
    (fun w lg => w = #(0 : w64) ∧ lg = true)
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
    hprog hpost
    (fun st e' st' hw _ hcall _ hp hat Hst => by
      obtain ⟨e, rfl, hr⟩ := renameStep_cases hw hcall hp.1 hp.2 hbs hbt (hsrcE st hat)
        (hneq st hp hat) Hst
      rcases hr with ⟨rfl, -⟩ | rfl
      · exact filesSame_metaEnd st k
      · exact (loggedFrom_metaDo st k s0 _).same)
    htree hE hE' Φ $$ Hinv Hsi [Hp Hp'] [Hn Hn'] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hp'
  · iapply (BigSepL.bigSepL_cons).2
    isplitl [Hn]
    · iexact Hn
    · iapply (BigSepL.bigSepL_singleton).2; iexact Hn'
  iintro %w Hq ⟨Hp, Hp'⟩ Hpost
  icases Hpost with (⟨%hW, -⟩ | ⟨%hW, %x, Hlg, Hl, -⟩)
  · exact absurd hW.2 (by simp)
  · obtain ⟨rfl, -⟩ := hW
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨Hn, Hl⟩
    icases (BigSepL.bigSepL_singleton).1 $$ Hl with Hn'
    icases osCallPerm_unchild R d bs _ j _ $$ Hp Hq with ⟨Hp, Hq⟩
    iapply HΦ $$ Hq Hp Hp'
    iexists x
    isplitl [Hlg]
    · iexact Hlg
    isplitl [Hn]
    · iexact Hn
    · iexact Hn'

/-- **`rename(2)` of the file `d/bs` onto `d'/bt`, its error witnessed** (`wp_osRenameFileS`, wal-fsfix2):
an errno only when the file system can fail on the target's path, or a path does not fit (the
witness `¬ (FsNoErrOn (· = child d' bt) ∧ PathFits … ∧ PathFits …)`). -/
theorem wp_osRenameFileSW (R : Roots) (d bs d' bt : GoString) (j j' i : Ino) (N N' : NameSet)
    (dq dq' : DFrac) (h h' : NamesH) (k s0 : Nat) (q : Qp) (hbs : NameOk bs) (hbt : NameOk bt)
    (hN : N.Mem bs) (hN' : N'.Mem bt) (hkey : (j, N) ≠ (j', N'))
    (hsrc : h.cur !! bs = some (.file i)) (htgt : ∀ J, h'.cur !! bt ≠ some (.dir J))
    (hs : h.next ≤ s0) (hs' : h'.next ≤ s0) (hsr : SameRootR R (child d bs) (child d' bt))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osPathS (L := L) R d' dq' j' -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osNames (L := L) j' N' (DFrac.own 1) h' -∗
      osCallS (L := L) k s0 (child d bs) q -∗
      (∀ e : w64, osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        osPathS (L := L) R d' dq' j' -∗
                ((⌜e ≠ 0⌝ ∗ osNames (L := L) j N (DFrac.own 1) h ∗ osNames (L := L) j' N' (DFrac.own 1) h') ∨
         ∃ x, osLogged (L := L) x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) ∗
           osNames (L := L) j N (DFrac.own 1) (h.log x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) (GMap.delete bs h.cur)) ∗
           osNames (L := L) j' N' (DFrac.own 1) (h'.log x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) (<[bt := .file i]> h'.cur))) -∗
        ⌜e ≠ 0 → ¬ (FsNoErrOn (· = child d' bt) ∧ PathFits (child d bs) ∧ PathFits (child d' bt))⌝ -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d' bt)))))) @ s; E {{ Φ }} := by
  iintro #Hos #Hsi Hp Hp' Hn1 Hn2 Hk HΦ
  by_cases hW : FsNoErrOn (· = child d' bt) ∧ PathFits (child d bs) ∧ PathFits (child d' bt)
  · obtain ⟨⟨Sio, -, h1, -, hp⟩, hf1, hf2⟩ := hW
    iapply wp_osRenameFileSNE Sio R d bs d' bt j j' i N N' dq dq' h h' k s0 q hbs
      hbt hN hN' hkey hsrc htgt hs hs' hsr (.inr (hp _ rfl)) ⟨hf1, hf2⟩ hE hE' Φ $$ Hos Hsi Hp Hp' Hn1 Hn2 Hk
    iintro Hperm Hp Hp' Hl
    iapply HΦ $$ Hperm Hp Hp' [Hl]
    · iright; iexact Hl
    ipureintro; intro h0; exact absurd rfl h0
  · iapply wp_osRenameFileS R d bs d' bt j j' i N N' dq dq' h h' k s0 q hbs hbt hN hN' hkey hsrc
      htgt hs hs' hsr hE hE' Φ $$ Hos Hsi Hp Hp' Hn1 Hn2 Hk
    iintro %e Hperm Hp Hp' Hres
    iapply HΦ $$ Hperm Hp Hp' Hres
    ipureintro; intro _; exact hW

end specs

end Fs
end Perennial

end
