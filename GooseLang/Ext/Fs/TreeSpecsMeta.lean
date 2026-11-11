/-
WP specs of the directory tree's metadata steps (`Impl.lean`): `Unlink`, `Rmdir`, `Mkdir`, `Rename`
(of a file; of a directory onto an absent name in the same directory; of an absent source, the
retry case). Untrusted.

Each takes the caller's fraction `q1` of the tree's history and its call `osCall k s q`, with
`q1 + q = 1`: the step holds the whole history (`wp_metaStep`), so no directory fd is open and no
other call is in flight, and the new history is the old one, or the old one with the step's
operation logged (`Hist.push`), its start the old history's length (the log stays `Sequential`).
What a path names is `lookupH R V p`; the specs name the directory a path is in by the path's
parent, `d`, of inode `j` (`lookupH R V d = some (.dir j)`).
-/
module

public import GooseLang.Ext.Fs.TreeSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## What a metadata step finds and leaves -/

/-- A state a metadata step of the call `k` (begun at `s'`) runs in, with the roots `R` and the
history `V`, the caller holding all of it: no directory fd, no other call. -/
structure MetaPre (st : OsState) (R : Roots) (V : Hist) (k s' : Nat) : Prop where
  wf : FsTreeWf st
  roots : st.fs.roots = R
  hist : V = (st.fs.treeDur, st.fs.metaLog)
  calls : st.proc.calls = {[k := s']}
  start : s' = st.fs.metaLog.length
  dfds : st.proc.dfds = ∅
  seq : Sequential st.fs.metaLog

/-- What a metadata step leaves: the files' part unchanged, the tree well formed, no call, no
directory fd, the log sequential. -/
structure MetaPost (st st' : OsState) : Prop where
  same : FilesSame st st'
  wf : FsTreeWf st'
  roots : st'.fs.roots = st.fs.roots
  calls : st'.proc.calls = ∅
  dfds : st'.proc.dfds = ∅
  seq : Sequential st'.fs.metaLog

/-! ## Pure facts of the metadata steps -/

theorem delete_singleton_self (k v : Nat) : GMap.delete k ({[k := v]} : GMap Nat Nat) = ∅ := by
  apply GMap.ext; intro t
  by_cases h : k = t
  · subst h; simp
  · simp [h]

theorem fmap_empty {A B : Type} (f : A → B) : GMap.fmap f (∅ : GMap w64 A) = ∅ := by
  apply GMap.ext; intro t; simp

theorem tree_full (st : OsState) :
    replay ((st.fs.metaLog.take st.fs.metaLog.length).map (·.op)) st.fs.treeDur = st.tree := by
  rw [List.take_length]; rfl

theorem wf_tree {st : OsState} (hw : FsTreeWf st) : TreeWf st.fs.roots st.tree ∧
    (∀ i, Named st.tree i → ∃ f, st.fs.files !! i = some f) ∧
    (∀ j, j ∈ st.tree → j < st.fs.nextIno) := by
  have := hw.hist _ (Nat.le_refl _); rwa [tree_full] at this

theorem mem_of_reach {R : Roots} {m : Tree} (hw : TreeWf R m) {j : Ino} (h : Reach R m j) : j ∈ m :=
  hw.1 j h

/-- After a metadata step that changed nothing: the call ended. -/
theorem metaPost_end {st : OsState} {R : Roots} {V : Hist} {k s' : Nat} (hp : MetaPre st R V k s') :
    MetaPost st (st.metaEnd k) ∧ ((st.metaEnd k).fs.treeDur, (st.metaEnd k).fs.metaLog) = V := by
  refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨hp.wf.roots, hp.wf.hist, hp.wf.dfds, hp.wf.disj, hp.wf.files_lt⟩,
    rfl, ?_, hp.dfds, hp.seq⟩, hp.hist.symm⟩
  show GMap.delete k st.proc.calls = ∅
  rw [hp.calls, delete_singleton_self]

/-- After a metadata step that logged `o`, from a state `st1` that is `st` with the call ended (and
maybe the inode counter moved), given what `o` makes of the tree. -/
theorem metaPost_do {st st1 : OsState} {R : Roots} {V : Hist} {k s' : Nat} (hp : MetaPre st R V k s')
    (o : MetaOp) (hf : st1.fs.files = st.fs.files) (hfd : st1.proc.fds = st.proc.fds)
    (hin : st1.proc.inflight = st.proc.inflight) (hm : st1.proc.maps = st.proc.maps)
    (hro : st1.fs.roots = st.fs.roots) (hdu : st1.fs.treeDur = st.fs.treeDur)
    (hlo : st1.fs.metaLog = st.fs.metaLog) (hca : st1.proc.calls = ∅) (hdf : st1.proc.dfds = ∅)
    (hni : st.fs.nextIno ≤ st1.fs.nextIno)
    (htw : TreeWf st.fs.roots (o.apply st.tree)) (hnm : ∀ i, Named (o.apply st.tree) i → Named st.tree i)
    (hlt : ∀ j, j ∈ o.apply st.tree → j < st1.fs.nextIno)
    (hst : st1.fs.stamp = st.fs.stamp := by rfl) :
    MetaPost st (st1.metaDo o s') ∧
      ((st1.metaDo o s').fs.treeDur, (st1.metaDo o s').fs.metaLog) = V.push ⟨o, V.2.length⟩ := by
  obtain ⟨-, hnamed, -⟩ := wf_tree hp.wf
  have hdfds' : (st1.metaDo o s').proc.dfds = ∅ := by
    simp only [OsState.metaDo, hdf, fmap_empty]
  refine ⟨⟨⟨by simp [OsState.metaDo, hf], by simp [OsState.metaDo, hfd], by simp [OsState.metaDo, hin],
    by simp [OsState.metaDo, hm], by simp [OsState.metaDo, hst]⟩, ?_, by simp [OsState.metaDo, hro],
    by simp [OsState.metaDo, hca],
    hdfds', ?_⟩, ?_⟩
  · refine fsTreeWf_meta hp.wf (o := o) (s := s') (by simp [OsState.metaDo, hro])
      (by simp [OsState.metaDo, hdu]) (by simp [OsState.metaDo, hlo])
      (fun i f h => ⟨f, by simp [OsState.metaDo, hf, h]⟩) (by simp [OsState.metaDo]; exact hni)
      htw (fun i hi => by
        obtain ⟨f, hf'⟩ := hnamed i (hnm i hi)
        exact ⟨f, by simp [OsState.metaDo, hf, hf']⟩)
      (fun j hj => by simp [OsState.metaDo]; exact hlt j hj)
      (fun fd df h => by rw [hdfds'] at h; simp at h)
      (fun fd _ => by rw [hdfds']; simp)
      (fun i hi => by
        simp only [OsState.metaDo, hf] at hi ⊢
        exact Nat.lt_of_lt_of_le (hp.wf.files_lt i hi) hni)
  · simp only [OsState.metaDo, hlo]
    rw [hp.start]; exact sequential_snoc hp.seq
  · simp only [OsState.metaDo, hdu, hlo, Hist.push]
    rw [hp.hist, hp.start]

/-- A removal names no new file. -/
theorem named_remove (m : Tree) (j : Ino) (b : GoString) (n : Node) (i : Ino) :
    Named ((MetaOp.remove j b n).apply m) i → Named m i := by
  rintro ⟨x, c, h⟩
  simp only [MetaOp.apply] at h
  rw [entry_upd] at h
  split at h
  · by_cases hb : b = c
    · subst hb; simp at h
    · rw [GMap.lookup_delete_ne _ hb, getD_lookup] at h
      exact ⟨j, c, h⟩
  · exact ⟨x, c, h⟩

/-- A new directory names no new file. -/
theorem named_mkdir (m : Tree) (j : Ino) (b : GoString) (J : Ino) (i : Ino) :
    Named ((MetaOp.mkdir j b J).apply m) i → Named m i := by
  rintro ⟨x, c, h⟩
  simp only [MetaOp.apply, Tree.entry] at h
  by_cases hx : J = x
  · subst hx; simp at h
  · rw [GMap.lookup_insert_ne _ _ hx] at h
    have h' : (m.upd j (fun d => <[b := Node.dir J]> d)).entry x c = some (.file i) := h
    rw [entry_upd] at h'
    split at h'
    · by_cases hb : b = c
      · subst hb; simp at h'
      · rw [GMap.lookup_insert_ne _ _ hb, getD_lookup] at h'
        exact ⟨j, c, h'⟩
    · exact ⟨x, c, h'⟩

/-- A rename names no new file (it moves an entry). -/
theorem named_rename (m : Tree) (j : Ino) (b : GoString) (j' : Ino) (b' : GoString) (n : Node)
    (old : Option Node) (i : Ino) :
    Named ((MetaOp.rename j b j' b' n old).apply m) i → Named m i := by
  rintro ⟨x, c, h⟩
  simp only [MetaOp.apply] at h
  split at h
  · rename_i n0 hn0
    rw [entry_upd] at h
    split at h
    · rename_i hjx
      by_cases hb : b' = c
      · subst hb; simp at h; subst h; exact ⟨j, b, hn0⟩
      · rw [GMap.lookup_insert_ne _ _ hb, getD_lookup] at h
        exact named_remove m j b n i ⟨j', c, h⟩
    · exact named_remove m j b n i ⟨x, c, by simpa [MetaOp.apply] using h⟩
  · exact ⟨x, c, h⟩

/-- The directories after a removal or a rename: those before, and the directories it changes. -/
theorem mem_remove (m : Tree) (j : Ino) (b : GoString) (n : Node) (x : Ino)
    (h : x ∈ (MetaOp.remove j b n).apply m) : x = j ∨ x ∈ m := by
  simp only [MetaOp.apply] at h; rw [mem_upd] at h
  rcases h with h | h
  · exact .inl h.symm
  · exact .inr h

theorem mem_rename (m : Tree) (j : Ino) (b : GoString) (j' : Ino) (b' : GoString) (n : Node)
    (old : Option Node) (x : Ino) (h : x ∈ (MetaOp.rename j b j' b' n old).apply m) :
    x = j ∨ x = j' ∨ x ∈ m := by
  simp only [MetaOp.apply] at h
  split at h
  · rw [mem_upd, mem_upd] at h
    rcases h with h | h | h
    · exact .inr (.inl h.symm)
    · exact .inl h.symm
    · exact .inr (.inr h)
  · exact .inr (.inr h)

theorem mem_mkdir (m : Tree) (j : Ino) (b : GoString) (J : Ino) (x : Ino)
    (h : x ∈ (MetaOp.mkdir j b J).apply m) : x = J ∨ x = j ∨ x ∈ m := by
  simp only [MetaOp.apply] at h
  rw [GMap.mem_iff] at h
  by_cases hx : J = x
  · exact .inl hx.symm
  · rw [GMap.lookup_insert_ne _ _ hx, ← GMap.mem_iff, mem_upd] at h
    rcases h with h | h
    · exact .inr (.inl h.symm)
    · exact .inr (.inr h)

/-- The state's lookups, as a spec states them. -/
theorem lookup_pre {st : OsState} {R : Roots} {V : Hist} {k s' : Nat} (hp : MetaPre st R V k s')
    (p : GoString) : st.lookup p = lookupH R V p := by
  rw [lookupH_eq st p, hp.roots, ← hp.hist]


/-- `metaPost_do` from the state with the call ended. -/
theorem metaPost_doEnd {st : OsState} {R : Roots} {V : Hist} {k s' : Nat} (hp : MetaPre st R V k s')
    (o : MetaOp) (htw : TreeWf st.fs.roots (o.apply st.tree))
    (hnm : ∀ i, Named (o.apply st.tree) i → Named st.tree i)
    (hlt : ∀ j, j ∈ o.apply st.tree → j < st.fs.nextIno) :
    MetaPost st ((st.metaEnd k).metaDo o s') ∧
      (((st.metaEnd k).metaDo o s').fs.treeDur, ((st.metaEnd k).metaDo o s').fs.metaLog) =
        V.push ⟨o, V.2.length⟩ :=
  metaPost_do hp o rfl rfl rfl rfl rfl rfl rfl
    (by show GMap.delete k st.proc.calls = ∅; rw [hp.calls, delete_singleton_self]) hp.dfds
    (Nat.le_refl _) htw hnm hlt

/-- `metaPost_do` from the state with the call ended and the next inode taken. -/
theorem metaPost_doIno {st : OsState} {R : Roots} {V : Hist} {k s' : Nat} (hp : MetaPre st R V k s')
    (o : MetaOp) (htw : TreeWf st.fs.roots (o.apply st.tree))
    (hnm : ∀ i, Named (o.apply st.tree) i → Named st.tree i)
    (hlt : ∀ j, j ∈ o.apply st.tree → j < st.fs.nextIno + 1) :
    MetaPost st ((st.metaEnd k).takeIno.metaDo o s') ∧
      (((st.metaEnd k).takeIno.metaDo o s').fs.treeDur,
        ((st.metaEnd k).takeIno.metaDo o s').fs.metaLog) = V.push ⟨o, V.2.length⟩ :=
  metaPost_do hp o rfl rfl rfl rfl rfl rfl rfl
    (by show GMap.delete k st.proc.calls = ∅; rw [hp.calls, delete_singleton_self]) hp.dfds
    (Nat.le_succ _) htw hnm hlt

/-- The token and the path of a step's value. -/
theorem tokPath_inj [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] {k k' : Nat} {p p' : GoString}
    (h : PairV (osTokV k') (#p') = PairV (osTokV k) (#p)) : k' = k ∧ p' = p := by
  injection h with h1 h2
  refine ⟨?_, go.intoVal_inj h2⟩
  injection h1 with h1; exact extVal_inj h1

theorem start_eq {st : OsState} {R : Roots} {V : Hist} {k s' start : Nat}
    (hp : MetaPre st R V k s') (h : st.proc.calls !! k = some start) : start = s' := by
  rw [hp.calls] at h; simp at h; exact h.symm

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **A metadata step**, from what it finds and leaves of the state (`hprog`: it can step; `hpost`:
each of its steps leaves an errno, a state as `MetaPost`, and the new history as `Q` says). -/
theorem wp_metaStep (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (V : Hist)
    (q1 q : Qp) (k s' : Nat) (hq : q1 + q = 1) (Q : w64 → Hist → Prop)
    (hprog : ∀ st, MetaPre st R V k s' → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', MetaPre st R V k s' → IsFsStep op v st e' st' →
      ∃ e : w64, e' = Val (#e) ∧ MetaPost st st' ∧ Q e (st'.fs.treeDur, st'.fs.metaLog))
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜Q e V'⌝ -∗ osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv Hh Hk HΦ
  iapply wp_fs_stepT op _ Φ hv hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %V0 %Γdf %Γc %h Hw Hn
  unfold osWorld treeWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod call_end _ _ Γc k s' q $$ HAd HAc Hcr Hk with ⟨%hk, HAd, HAc, Hcr, Hq⟩
  ihave Hwhole : osTree (L := L) (DFrac.own 1) st.fs.roots V $$ [Hh Hq]
  · rw [← hq]; iapply (osTree_split q1 q _ _).2; iframe
  icases whole_alone _ _ Γdf (GMap.delete k Γc) $$ Hwhole Hrd Hcr with ⟨%Hal, Hwhole, Hrd, Hcr⟩
  obtain ⟨hdf, hcl⟩ := Hal
  subst hdf
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcalls : st.proc.calls = {[k := s']} := by
    apply GMap.ext; intro t
    rw [← hc.calls t, GMap.lookup_singleton_iff]
    by_cases ht : k = t
    · subst ht; rw [hk]; simp
    · rw [if_neg ht]
      have := congrArg (· !! t) hcl
      simp only [GMap.lookup_delete_ne _ ht, GMap.lookup_empty] at this
      rw [this]; rfl
  have hpre : MetaPre st st.fs.roots V k s' :=
    ⟨hw, rfl, hc.hist, hcalls, hc.start k _ hk, dfds_empty hc, hc.seq⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', st', hs, hfs⟩ := hprog st hpre
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hfs Hag
    exact ⟨e', h, st', hs, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  obtain ⟨e, rfl, hpo, hQ⟩ := hpost st e' st' hpre Hst
  imod osWorld_filesSame (st := st) (st' := st') hpo.same Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh⟩
  imod osTree_update _ _ (st'.fs.treeDur, st'.fs.metaLog) _ _ $$ HAd Hwhole with ⟨HAd, Hwhole⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, (st'.fs.treeDur, st'.fs.metaLog), ∅, GMap.delete k Γc
  unfold osWorld
  isplitl [Hw]
  · iexact Hw
  isplitl [HAd HAdf HAc Hrd Hcr]
  · rw [hpo.roots]
    iframe
    ipureintro
    refine ⟨hpo.wf, ⟨rfl, hpo.seq, fun fd => ?_, fun fd x df hx => by simp at hx,
      fun fd x hx => by simp at hx, fun t => ?_, fun t x hx => by rw [hcl] at hx; simp at hx⟩⟩
    · rw [hpo.dfds]; simp
    · rw [hpo.calls, hcl]; simp
  iapply wp_value'
  iapply HΦ $$ %e %_ %hQ Hwhole

/-! ## `unlink(2)` -/

/-- What `unlink` of `d/b` leaves (`d` the directory `j`): a file removed (on a failure, removed or
not); or a failure, unchanged. -/
def UnlinkPost (R : Roots) (V : Hist) (d b : GoString) (j : Ino) (e : w64) (V' : Hist) : Prop :=
  (∃ i, lookupH R V (child d b) = some (.file i) ∧
    ((e = 0 ∧ V' = V.push ⟨.remove j b (.file i), V.2.length⟩) ∨
     (e ≠ 0 ∧ (V' = V ∨ V' = V.push ⟨.remove j b (.file i), V.2.length⟩)))) ∨
  (e ≠ 0 ∧ V' = V)

/-- **`unlink(2)`** of `d/b`, `d` the directory `j`, by the call `k`, with the rest of the history. -/
theorem wp_osUnlinkG (d b : GoString) (j : Ino) (hb : NameOk b) (R : Roots) (V : Hist) (q1 q : Qp)
    (k s' : Nat) (hq : q1 + q = 1) (hd : lookupH R V d = some (.dir j)) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜UnlinkPost R V d b j e V'⌝ -∗
        osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  refine wp_metaStep "Unlink" _ (by simp [val.isPanic]) R V q1 q k s' hq _ ?_ ?_ hE Φ
  · intro st hp
    have hd' : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    exact ⟨_, st.metaEnd k, ⟨child d b, k, s', rfl, treeName_child hd' hb,
      by rw [hp.calls]; simp, .inr ⟨W64 1, by decide, rfl, rfl⟩⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro st e' st' hp hst
    have hd' : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    have hroots := hp.wf.roots
    obtain ⟨htw, -, hlt⟩ := wf_tree hp.wf
    obtain ⟨p, k', start, hv, -, hk', hres⟩ := hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    obtain rfl := start_eq hp hk'
    rcases hres with ⟨i, j0, b0, hfi, hpar, hr⟩ | ⟨e, he, rfl, rfl⟩
    · rw [parent_child hd' hb] at hpar
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpar)
      have hent : st.tree.entry j b = some (.file i) := by rw [← lookup_child hroots hd' hb]; exact hfi
      have hfi' : lookupH R V (child d b) = some (.file i) := (lookup_pre hp _).symm.trans hfi
      have hpost := metaPost_doEnd hp (.remove j b (.file i))
        (treeWf_removeFile htw (reach_of_lookup hd') hent _) (named_remove _ _ _ _)
        (fun x hx => by
          rcases mem_remove _ _ _ _ _ hx with rfl | hx
          · exact hlt _ (mem_of_reach htw (reach_of_lookup hd'))
          · exact hlt _ hx)
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨0, rfl, hpost.1, .inl ⟨i, hfi', .inl ⟨rfl, hpost.2⟩⟩⟩
      · exact ⟨e, rfl, (metaPost_end hp).1, .inl ⟨i, hfi', .inr ⟨he, .inl (metaPost_end hp).2⟩⟩⟩
      · exact ⟨e, rfl, hpost.1, .inl ⟨i, hfi', .inr ⟨he, .inr hpost.2⟩⟩⟩
    · exact ⟨e, rfl, (metaPost_end hp).1, .inr ⟨he, (metaPost_end hp).2⟩⟩


/-! ## `rmdir(2)` -/

/-- What `rmdir` of `d/b` leaves (`d` the directory `j`): an empty directory removed (on a failure,
removed or not); or a failure, unchanged. -/
def RmdirPost (R : Roots) (V : Hist) (d b : GoString) (j : Ino) (e : w64) (V' : Hist) : Prop :=
  (∃ J, lookupH R V (child d b) = some (.dir J) ∧ (∀ c, V.now.entry J c = none) ∧
    ((e = 0 ∧ V' = V.push ⟨.remove j b (.dir J), V.2.length⟩) ∨
     (e ≠ 0 ∧ (V' = V ∨ V' = V.push ⟨.remove j b (.dir J), V.2.length⟩)))) ∨
  (e ≠ 0 ∧ V' = V)

/-- **`rmdir(2)`** of `d/b`, `d` the directory `j`, by the call `k`, with the rest of the history (an
fd may be open on the directory: it keeps it, empty). -/
theorem wp_osRmdirG (d b : GoString) (j : Ino) (hb : NameOk b) (R : Roots) (V : Hist) (q1 q : Qp)
    (k s' : Nat) (hq : q1 + q = 1) (hd : lookupH R V d = some (.dir j)) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜RmdirPost R V d b j e V'⌝ -∗
        osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  refine wp_metaStep "Rmdir" _ (by simp [val.isPanic]) R V q1 q k s' hq _ ?_ ?_ hE Φ
  · intro st hp
    have hd' : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    exact ⟨_, st.metaEnd k, ⟨child d b, k, s', rfl, treeName_child hd' hb,
      by rw [hp.calls]; simp, .inr ⟨W64 1, by decide, rfl, rfl⟩⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro st e' st' hp hst
    have hd' : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    have hroots := hp.wf.roots
    obtain ⟨htw, -, hlt⟩ := wf_tree hp.wf
    obtain ⟨p, k', start, hv, -, hk', hres⟩ := hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    obtain rfl := start_eq hp hk'
    rcases hres with ⟨J, j0, b0, ⟨hJ, hemp⟩, hpar, hr⟩ | ⟨e, he, rfl, rfl⟩
    · rw [parent_child hd' hb] at hpar
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpar)
      have hent : st.tree.entry j b = some (.dir J) := by rw [← lookup_child hroots hd' hb]; exact hJ
      have hJ' : lookupH R V (child d b) = some (.dir J) := (lookup_pre hp _).symm.trans hJ
      have hemp' : ∀ c, V.now.entry J c = none := by rw [hp.hist]; exact hemp
      have hpost := metaPost_doEnd hp (.remove j b (.dir J))
        (treeWf_rmdir htw (reach_of_lookup hd') hent hemp _) (named_remove _ _ _ _)
        (fun x hx => by
          rcases mem_remove _ _ _ _ _ hx with rfl | hx
          · exact hlt _ (mem_of_reach htw (reach_of_lookup hd'))
          · exact hlt _ hx)
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨0, rfl, hpost.1, .inl ⟨J, hJ', hemp', .inl ⟨rfl, hpost.2⟩⟩⟩
      · exact ⟨e, rfl, (metaPost_end hp).1, .inl ⟨J, hJ', hemp', .inr ⟨he, .inl (metaPost_end hp).2⟩⟩⟩
      · exact ⟨e, rfl, hpost.1, .inl ⟨J, hJ', hemp', .inr ⟨he, .inr hpost.2⟩⟩⟩
    · exact ⟨e, rfl, (metaPost_end hp).1, .inr ⟨he, (metaPost_end hp).2⟩⟩

/-! ## `mkdir(2)` -/

/-- What `mkdir` of `d/b` leaves (`d` the directory `j`): where nothing was, a new, empty directory
of an inode no directory of the tree or root has (on a failure, made or not); or a failure,
unchanged. -/
def MkdirPost (R : Roots) (V : Hist) (d b : GoString) (j : Ino) (e : w64) (V' : Hist) : Prop :=
  (lookupH R V (child d b) = none ∧ ∃ J, J ∉ V.now ∧ (∀ r, (r, J) ∉ R) ∧
    ((e = 0 ∧ V' = V.push ⟨.mkdir j b J, V.2.length⟩) ∨
     (e ≠ 0 ∧ (V' = V ∨ V' = V.push ⟨.mkdir j b J, V.2.length⟩)))) ∨
  (e ≠ 0 ∧ V' = V)

/-- **`mkdir(2)`** of `d/b`, `d` the directory `j`, by the call `k`, with the rest of the history. -/
theorem wp_osMkdirG (d b : GoString) (j : Ino) (hb : NameOk b) (R : Roots) (V : Hist) (q1 q : Qp)
    (k s' : Nat) (hq : q1 + q = 1) (hd : lookupH R V d = some (.dir j)) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜MkdirPost R V d b j e V'⌝ -∗
        osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Mkdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  refine wp_metaStep "Mkdir" _ (by simp [val.isPanic]) R V q1 q k s' hq _ ?_ ?_ hE Φ
  · intro st hp
    have hd' : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    exact ⟨_, st.metaEnd k, ⟨child d b, k, s', rfl, treeName_child hd' hb,
      by rw [hp.calls]; simp, .inr ⟨W64 1, by decide, rfl, rfl⟩⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro st e' st' hp hst
    have hd' : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    have hroots := hp.wf.roots
    obtain ⟨htw, -, hlt⟩ := wf_tree hp.wf
    obtain ⟨p, k', start, hv, -, hk', hres⟩ := hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    obtain rfl := start_eq hp hk'
    rcases hres with ⟨j0, b0, hnone, hpar, hr⟩ | ⟨e, he, rfl, rfl⟩
    · rw [parent_child hd' hb] at hpar
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpar)
      have hent : st.tree.entry j b = none := by rw [← lookup_child hroots hd' hb]; exact hnone
      have hnone' : lookupH R V (child d b) = none := (lookup_pre hp _).symm.trans hnone
      have hJm : st.fs.nextIno ∉ st.tree := fun h => Nat.lt_irrefl _ (hlt _ h)
      have hJr : ∀ r, (r, st.fs.nextIno) ∉ st.fs.roots := fun r h =>
        hJm (mem_of_reach htw (.root r _ h))
      have hJm' : st.fs.nextIno ∉ V.now := by rw [hp.hist]; exact hJm
      have hJr' : ∀ r, (r, st.fs.nextIno) ∉ R := by rw [← hp.roots]; exact hJr
      have hpost := metaPost_doIno hp (.mkdir j b st.fs.nextIno)
        (treeWf_mkdir htw (reach_of_lookup hd') hb hent hJm hJr) (named_mkdir _ _ _ _)
        (fun x hx => by
          rcases mem_mkdir _ _ _ _ _ hx with rfl | rfl | hx
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (hlt _ (mem_of_reach htw (reach_of_lookup hd')))
          · exact Nat.lt_succ_of_lt (hlt _ hx))
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨0, rfl, hpost.1, .inl ⟨hnone', _, hJm', hJr', .inl ⟨rfl, hpost.2⟩⟩⟩
      · exact ⟨e, rfl, (metaPost_end hp).1,
          .inl ⟨hnone', _, hJm', hJr', .inr ⟨he, .inl (metaPost_end hp).2⟩⟩⟩
      · exact ⟨e, rfl, hpost.1, .inl ⟨hnone', _, hJm', hJr', .inr ⟨he, .inr hpost.2⟩⟩⟩
    · exact ⟨e, rfl, (metaPost_end hp).1, .inr ⟨he, (metaPost_end hp).2⟩⟩


/-! ## `rename(2)` -/

/-- What a rename of `d/bs` (`d` the directory `j`) to `d'/bt` (`d'` the directory `j'`) logs, the
source naming `n`. -/
def renameOp (R : Roots) (V : Hist) (j : Ino) (bs : GoString) (j' : Ino) (d' bt : GoString)
    (n : Node) : MetaOp :=
  .rename j bs j' bt n (lookupH R V (child d' bt))

/-- What a rename leaves: the operation logged (on a failure, logged or not), the history unchanged
(a rename of an entry to itself, or a failure). -/
def RenamePost (V : Hist) (o : MetaOp) (e : w64) (V' : Hist) : Prop :=
  (e = 0 ∧ V' = V.push ⟨o, V.2.length⟩) ∨
  (e ≠ 0 ∧ (V' = V ∨ V' = V.push ⟨o, V.2.length⟩)) ∨
  (e = 0 ∧ V' = V)

theorem tokPair_inj [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] {k k' : Nat}
    {a a' b b' : GoString}
    (h : PairV (osTokV k') (PairV (#a') (#b')) = PairV (osTokV k) (PairV (#a) (#b))) :
    k' = k ∧ a' = a ∧ b' = b := by
  injection h with h1 h2
  injection h2 with h3 h4
  refine ⟨?_, go.intoVal_inj h3, go.intoVal_inj h4⟩
  injection h1 with h1; exact extVal_inj h1

theorem not_isUnder_child_self (d b : GoString) : ¬ IsUnder (child d b) d := by
  intro h
  rcases h with h | h
  · have := congrArg List.length h; simp at this
  · have := h.length_le; simp at this; omega

theorem child_inj {d b b' : GoString} (h : child d b = child d b') : b = b' := by
  have := List.append_cancel_left h; simpa using this

/-- The rename's step from what the spec knows of the source's and target's directories. -/
theorem renameOp_eq {st : OsState} {R : Roots} {V : Hist} {k s' : Nat} (hp : MetaPre st R V k s')
    {d bs d' bt : GoString} {j j' : Ino} (hbs : NameOk bs) (hbt : NameOk bt)
    (hd : st.lookup d = some (.dir j)) (hd' : st.lookup d' = some (.dir j')) {n : Node}
    (hs : st.lookup (child d bs) = some n) {o : MetaOp}
    (ho : RenameOp st (child d bs) (child d' bt) o) : o = renameOp R V j bs j' d' bt n := by
  obtain ⟨js, bs', jt, bt', n', h1, h2, h3, rfl⟩ := ho
  rw [parent_child hd hbs] at h1; rw [parent_child hd' hbt] at h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
  rw [hs] at h3; cases h3
  simp only [renameOp, ← lookup_pre hp]

/-- **`rename(2)` of a file** `d/bs` (`d` the directory `j`) to `d'/bt` (`d'` the directory `j'`),
which names no directory, by the call `k`, with the rest of the history. -/
theorem wp_osRenameFileG (d bs d' bt : GoString) (j j' i : Ino) (hbs : NameOk bs) (hbt : NameOk bt)
    (R : Roots) (V : Hist) (q1 q : Qp) (k s' : Nat) (hq : q1 + q = 1)
    (hd : lookupH R V d = some (.dir j)) (hd' : lookupH R V d' = some (.dir j'))
    (hs : lookupH R V (child d bs) = some (.file i))
    (ht : ∀ J, lookupH R V (child d' bt) ≠ some (.dir J)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜RenamePost V (renameOp R V j bs j' d' bt (.file i)) e V'⌝ -∗
        osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename"
        (Val (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))))) @ s; E {{ Φ }} := by
  refine wp_metaStep "Rename" _ (by simp [val.isPanic]) R V q1 q k s' hq _ ?_ ?_ hE Φ
  · intro st hp
    have hdd : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    have hdd' : st.lookup d' = some (.dir j') := (lookup_pre hp d').trans hd'
    exact ⟨_, st.metaEnd k, ⟨child d bs, child d' bt, k, s', rfl, treeName_child hdd hbs,
      treeName_child hdd' hbt, by rw [hp.calls]; simp,
      fun _ k'' s'' h => by rw [hp.calls] at h; simp at h; exact h.1.symm,
      .inr (.inr ⟨W64 1, by decide, rfl, rfl⟩)⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro st e' st' hp hst
    have hdd : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    have hdd' : st.lookup d' = some (.dir j') := (lookup_pre hp d').trans hd'
    have hss : st.lookup (child d bs) = some (.file i) := (lookup_pre hp _).trans hs
    have hroots := hp.wf.roots
    obtain ⟨htw, -, hlt⟩ := wf_tree hp.wf
    obtain ⟨s0, t0, k', start, hv, -, -, hk', -, hres⟩ := hst
    obtain ⟨rfl, rfl, rfl⟩ := tokPair_inj hv
    obtain rfl := start_eq hp hk'
    rcases hres with ⟨-, o, ho, hr⟩ | ⟨-, -, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩
    · obtain rfl := renameOp_eq hp hbs hbt hdd hdd' hss ho
      have hent : st.tree.entry j bs = some (.file i) := by
        rw [← lookup_child hroots hdd hbs]; exact hss
      have hnt : ∀ J, st.tree.entry j' bt ≠ some (.dir J) := fun J => by
        rw [← lookup_child hroots hdd' hbt, lookup_pre hp]; exact ht J
      have hpost := metaPost_doEnd hp (renameOp R V j bs j' d' bt (.file i))
        (treeWf_renameFile htw (reach_of_lookup hdd) (reach_of_lookup hdd') hbt hent hnt _ _)
        (named_rename _ _ _ _ _ _ _)
        (fun x hx => by
          rcases mem_rename _ _ _ _ _ _ _ _ hx with rfl | rfl | hx
          · exact hlt _ (mem_of_reach htw (reach_of_lookup hdd))
          · exact hlt _ (mem_of_reach htw (reach_of_lookup hdd'))
          · exact hlt _ hx)
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨0, rfl, hpost.1, .inl ⟨rfl, hpost.2⟩⟩
      · exact ⟨e, rfl, (metaPost_end hp).1, .inr (.inl ⟨he, .inl (metaPost_end hp).2⟩)⟩
      · exact ⟨e, rfl, hpost.1, .inr (.inl ⟨he, .inr hpost.2⟩)⟩
    · exact ⟨0, rfl, (metaPost_end hp).1, .inr (.inr ⟨rfl, (metaPost_end hp).2⟩)⟩
    · exact ⟨e, rfl, (metaPost_end hp).1, .inr (.inl ⟨he, .inl (metaPost_end hp).2⟩)⟩

/-- What a directory's rename leaves: the operation logged (on a failure, logged or not). -/
def RenameDirPost (V : Hist) (o : MetaOp) (e : w64) (V' : Hist) : Prop :=
  (e = 0 ∧ V' = V.push ⟨o, V.2.length⟩) ∨ (e ≠ 0 ∧ (V' = V ∨ V' = V.push ⟨o, V.2.length⟩))

/-- **`rename(2)` of a directory** `d/bs` (`d` the directory `j`; the source the directory `J`) to
`d/bt`, absent, by the call `k`, with the rest of the history (so no other call is in flight). -/
theorem wp_osRenameDirG (d bs bt : GoString) (j J : Ino) (hbs : NameOk bs) (hbt : NameOk bt)
    (hne : bs ≠ bt) (R : Roots) (V : Hist) (q1 q : Qp) (k s' : Nat) (hq : q1 + q = 1)
    (hd : lookupH R V d = some (.dir j)) (hs : lookupH R V (child d bs) = some (.dir J))
    (ht : lookupH R V (child d bt) = none) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜RenameDirPost V (.rename j bs j bt (.dir J) none) e V'⌝ -∗
        osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename"
        (Val (PairV (osTokV k) (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} := by
  refine wp_metaStep "Rename" _ (by simp [val.isPanic]) R V q1 q k s' hq _ ?_ ?_ hE Φ
  · intro st hp
    have hdd : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    exact ⟨_, st.metaEnd k, ⟨child d bs, child d bt, k, s', rfl, treeName_child hdd hbs,
      treeName_child hdd hbt, by rw [hp.calls]; simp,
      fun _ k'' s'' h => by rw [hp.calls] at h; simp at h; exact h.1.symm,
      .inr (.inr ⟨W64 1, by decide, rfl, rfl⟩)⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro st e' st' hp hst
    have hdd : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    have hss : st.lookup (child d bs) = some (.dir J) := (lookup_pre hp _).trans hs
    have htt : st.lookup (child d bt) = none := (lookup_pre hp _).trans ht
    have hroots := hp.wf.roots
    obtain ⟨htw, -, hlt⟩ := wf_tree hp.wf
    obtain ⟨s0, t0, k', start, hv, -, -, hk', -, hres⟩ := hst
    obtain ⟨rfl, rfl, rfl⟩ := tokPair_inj hv
    obtain rfl := start_eq hp hk'
    rcases hres with ⟨-, o, ho, hr⟩ | ⟨hst', -, -, -⟩ | ⟨e, he, rfl, rfl⟩
    · have ho' := renameOp_eq hp hbs hbt hdd hdd hss ho
      simp only [renameOp, ht] at ho'
      subst ho'
      have hent : st.tree.entry j bs = some (.dir J) := by
        rw [← lookup_child hroots hdd hbs]; exact hss
      have hnt : st.tree.entry j bt = none := by rw [← lookup_child hroots hdd hbt]; exact htt
      have hnot : ¬ BelowP st.tree J j := fun hb =>
        not_isUnder_child_self d bs (isUnder_of_belowP hroots htw hss hdd hb)
      have hpost := metaPost_doEnd hp (.rename j bs j bt (.dir J) none)
        (treeWf_renameDir htw (reach_of_lookup hdd) (reach_of_lookup hdd) hbt hent
          (fun h => hne h.2) (.inl hnt) hnot _ _)
        (named_rename _ _ _ _ _ _ _)
        (fun x hx => by
          rcases mem_rename _ _ _ _ _ _ _ _ hx with rfl | rfl | hx
          · exact hlt _ (mem_of_reach htw (reach_of_lookup hdd))
          · exact hlt _ (mem_of_reach htw (reach_of_lookup hdd))
          · exact hlt _ hx)
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨0, rfl, hpost.1, .inl ⟨rfl, hpost.2⟩⟩
      · exact ⟨e, rfl, (metaPost_end hp).1, .inr ⟨he, .inl (metaPost_end hp).2⟩⟩
      · exact ⟨e, rfl, hpost.1, .inr ⟨he, .inr hpost.2⟩⟩
    · exact absurd (child_inj hst') hne
    · exact ⟨e, rfl, (metaPost_end hp).1, .inr ⟨he, .inl (metaPost_end hp).2⟩⟩

/-- **`rename(2)` of an absent source** `d/bs` (the retry of a rename that moved it) to `d'/bt`, by
the call `k`, with the rest of the history: it fails, unchanged. -/
theorem wp_osRenameAbsentG (d bs d' bt : GoString) (j j' : Ino) (hbs : NameOk bs) (hbt : NameOk bt)
    (R : Roots) (V : Hist) (q1 q : Qp) (k s' : Nat) (hq : q1 + q = 1)
    (hd : lookupH R V d = some (.dir j)) (hd' : lookupH R V d' = some (.dir j'))
    (hs : lookupH R V (child d bs) = none) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64), ⌜e ≠ 0⌝ -∗ osTree (L := L) (DFrac.own 1) R V -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename"
        (Val (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))))) @ s; E {{ Φ }} := by
  have hprog : ∀ st, MetaPre st R V k s' → ∃ e' st',
      IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st e' st' ∧
        FilesSame st st' := by
    intro st hp
    have hdd : st.lookup d = some (.dir j) := (lookup_pre hp d).trans hd
    have hdd' : st.lookup d' = some (.dir j') := (lookup_pre hp d').trans hd'
    exact ⟨_, st.metaEnd k, ⟨child d bs, child d' bt, k, s', rfl, treeName_child hdd hbs,
      treeName_child hdd' hbt, by rw [hp.calls]; simp,
      fun _ k'' s'' h => by rw [hp.calls] at h; simp at h; exact h.1.symm,
      .inr (.inr ⟨W64 1, by decide, rfl, rfl⟩)⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', MetaPre st R V k s' →
      IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st e' st' →
      ∃ e : w64, e' = Val (#e) ∧ MetaPost st st' ∧
        (fun (e : w64) (V' : Hist) => e ≠ 0 ∧ V' = V) e (st'.fs.treeDur, st'.fs.metaLog) := by
    intro st e' st' hp hst
    have hss : st.lookup (child d bs) = none := (lookup_pre hp _).trans hs
    obtain ⟨s0, t0, k', start, hv, -, -, hk', -, hres⟩ := hst
    obtain ⟨rfl, rfl, rfl⟩ := tokPair_inj hv
    obtain rfl := start_eq hp hk'
    rcases hres with ⟨hok, -⟩ | ⟨-, hn, -, -⟩ | ⟨e, he, rfl, rfl⟩
    · obtain ⟨-, -, -, hm⟩ := hok
      rw [hss] at hm; exact hm.elim
    · exact absurd hss hn
    · exact ⟨e, rfl, (metaPost_end hp).1, he, (metaPost_end hp).2⟩
  iintro #Hinv Hh Hk HΦ
  iapply wp_metaStep "Rename" _ (by simp [val.isPanic]) R V q1 q k s' hq
    (fun e V' => e ≠ 0 ∧ V' = V) hprog hpost hE Φ $$ Hinv Hh Hk
  iintro %e %V' %hQ HV
  obtain ⟨he, rfl⟩ := hQ
  iapply HΦ $$ %e %he HV

/-- **The entries after a directory's rename** in its directory `j`, onto an absent name: the
directory at the new name, nothing at the old, every other entry as it was. -/
theorem renameDir_entries (m : Tree) (j : Ino) (bs bt : GoString) (J : Ino) (hne : bs ≠ bt)
    (hs : m.entry j bs = some (.dir J)) (x : Ino) (c : GoString) :
    ((MetaOp.rename j bs j bt (.dir J) none).apply m).entry x c =
      if x = j ∧ c = bt then some (.dir J) else if x = j ∧ c = bs then none else m.entry x c := by
  simp only [MetaOp.apply, hs]
  rw [entry_upd]
  by_cases hx : j = x
  · subst hx
    simp only [if_pos rfl, Tree.upd, GMap.lookup_insert, Option.getD_some, true_and]
    by_cases hc : bt = c
    · subst hc; simp
    · rw [GMap.lookup_insert_ne _ _ hc, if_neg (Ne.symm hc)]
      by_cases hc' : bs = c
      · subst hc'; simp
      · rw [GMap.lookup_delete_ne _ hc', if_neg (Ne.symm hc'), getD_lookup]; rfl
  · rw [if_neg hx, entry_upd, if_neg hx]
    simp [Ne.symm hx]


end specs

end Fs
end Perennial

end
