/-
WP specs of the directory tree's steps (`Impl.lean`): calls on paths (`CallBegin`, and the token
each path step ends), `LstatDir`, `FdKind` of a directory fd, and the ghost lemmas the other tree
specs share (`TreeSpecs2.lean`, `TreeSpecs3.lean`, `TreeSpecsDir.lean`). Untrusted.

**Calls.** `CallBegin` takes a fraction `q` of the tree's history from its caller into the state
interpretation (`callRes`) and gives the token `osCall t s q`, `s` the history's length; the call's
step returns it. A metadata step needs the whole history: the caller's part and its call's.
**Paths.** A spec states where a path leads by `lookupH R V p`, the resolution of `p` with the
roots `R` over the history `V`'s tree, which is the state's (`lookupH_eq`).
-/
module

public import GooseLang.Ext.Fs.World
public import GooseLang.Ext.Fs.TreeLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Paths over the ghost history -/

/-- A state with the roots `R` and the history `V`'s tree (and nothing else): the one whose paths a
spec talks about. -/
def Hist.st (R : Roots) (V : Hist) : OsState :=
  { fs := { roots := R, treeDur := V.1, metaLog := V.2, committed := fun _ => False, files := ∅,
            nextIno := 0 },
    proc := ProcState.empty }

/-- What `p` names, with the roots `R`, in the history `V`'s tree now. -/
def lookupH (R : Roots) (V : Hist) (p : GoString) : Option Node := (Hist.st R V).lookup p

theorem tree_eq (st : OsState) : st.tree = (Hist.st st.fs.roots (st.fs.treeDur, st.fs.metaLog)).tree := rfl

theorem lookupH_eq (st : OsState) (p : GoString) :
    st.lookup p = lookupH st.fs.roots (st.fs.treeDur, st.fs.metaLog) p := rfl

theorem parentH_eq (st : OsState) (p : GoString) :
    st.parent p = (Hist.st st.fs.roots (st.fs.treeDur, st.fs.metaLog)).parent p := rfl

theorem treeName_eq (st : OsState) (p : GoString) :
    st.TreeName p = (Hist.st st.fs.roots (st.fs.treeDur, st.fs.metaLog)).TreeName p := rfl

theorem treePath_eq (st : OsState) (p : GoString) :
    st.TreePath p = (Hist.st st.fs.roots (st.fs.treeDur, st.fs.metaLog)).TreePath p := rfl

theorem histSt_tree (R : Roots) (V : Hist) : (Hist.st R V).tree = V.now := rfl

/-! ## Fresh tokens -/

theorem le_sum_of_mem : ∀ (L : List Nat) (x : Nat), x ∈ L → x ≤ L.sum
  | [], _, h => absurd h List.not_mem_nil
  | a :: L, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem L x h; simp; omega

theorem exists_fresh2 {A B : Type} (M1 : GMap Nat A) (M2 : GMap Nat B) :
    ∃ t, M1 !! t = none ∧ M2 !! t = none := by
  let n := (M1.toList.map (·.1)).sum + (M2.toList.map (·.1)).sum + 1
  refine ⟨n, ?_, ?_⟩
  · cases h : M1 !! n with
    | none => rfl
    | some v =>
      have := le_sum_of_mem (M1.toList.map (·.1)) n
        (List.mem_map.2 ⟨(n, v), (GMap.mem_toList _ _ _).2 h, rfl⟩)
      omega
  · cases h : M2 !! n with
    | none => rfl
    | some v =>
      have := le_sum_of_mem (M2.toList.map (·.1)) n
        (List.mem_map.2 ⟨(n, v), (GMap.mem_toList _ _ _).2 h, rfl⟩)
      omega


/-! ## A metadata step's state facts -/

theorem reach_of_walk {R : Roots} {m : Tree} : ∀ {cs : List GoString} {j x : Ino},
    Reach R m j → walk m (.dir j) cs = some (.dir x) → Reach R m x
  | [], j, x, hj, h => by simp [walk] at h; subst h; exact hj
  | c :: cs, j, x, hj, h => by
    simp only [walk] at h
    cases he : m.entry j c with
    | none => rw [he] at h; cases h
    | some n =>
      rw [he] at h; simp only at h
      cases n with
      | dir j' => exact reach_of_walk (.child j c j' hj he) h
      | file i => cases cs <;> simp [walk] at h

/-- A directory a path names is reachable from a root. -/
theorem reach_of_lookup {st : OsState} {p : GoString} {j : Ino}
    (h : st.lookup p = some (.dir j)) : Reach st.fs.roots st.tree j := by
  obtain ⟨r, j0, cs, hrj, -, -, hw⟩ := lookup_some h
  exact reach_of_walk (.root r j0 hrj) hw

/-- A file a path names is named in the tree. -/
theorem named_of_walk {m : Tree} : ∀ {cs : List GoString} {j i : Ino},
    walk m (.dir j) cs = some (.file i) → Named m i
  | [], _, _, h => by simp [walk] at h
  | c :: cs, j, i, h => by
    simp only [walk] at h
    cases he : m.entry j c with
    | none => rw [he] at h; cases h
    | some n =>
      rw [he] at h; simp only at h
      cases n with
      | dir j' => exact named_of_walk h
      | file i' => cases cs with
        | nil => simp [walk] at h; subst h; exact ⟨j, c, he⟩
        | cons _ _ => simp [walk] at h

theorem named_of_lookup {st : OsState} {p : GoString} {i : Ino}
    (h : st.lookup p = some (.file i)) : Named st.tree i := by
  obtain ⟨r, j0, cs, -, -, -, hw⟩ := lookup_some h
  exact named_of_walk hw

theorem apply_mem_mono (o : MetaOp) (m : Tree) (x : Ino) (h : x ∈ m) : x ∈ o.apply m := by
  cases o with
  | create j b i => simp only [MetaOp.apply]; rw [mem_upd]; exact .inr h
  | mkdir j b j' =>
    simp only [MetaOp.apply]; rw [GMap.mem_iff]
    by_cases hx : j' = x
    · subst hx; simp
    · rw [GMap.lookup_insert_ne _ _ hx, ← GMap.mem_iff, mem_upd]; exact .inr h
  | remove j b n => simp only [MetaOp.apply]; rw [mem_upd]; exact .inr h
  | rename j b j' b' n old =>
    simp only [MetaOp.apply]
    split
    · rw [mem_upd, mem_upd]; exact .inr (.inr h)
    · exact h

/-- **A logged operation keeps the tree well formed**, given what it makes of the tree now. -/
theorem fsTreeWf_meta {st st' : OsState} (hw : FsTreeWf st) {o : MetaOp} {s : Nat}
    (hroots : st'.fs.roots = st.fs.roots) (hdur : st'.fs.treeDur = st.fs.treeDur)
    (hlog : st'.fs.metaLog = st.fs.metaLog ++ [⟨o, s⟩])
    (hfiles : ∀ i f, st.fs.files !! i = some f → ∃ f', st'.fs.files !! i = some f')
    (hnext : st.fs.nextIno ≤ st'.fs.nextIno)
    (htw : TreeWf st.fs.roots (o.apply st.tree))
    (hnamed : ∀ i, Named (o.apply st.tree) i → ∃ f, st'.fs.files !! i = some f)
    (hlt : ∀ j, j ∈ o.apply st.tree → j < st'.fs.nextIno)
    (hdfds : ∀ fd df, st'.proc.dfds !! fd = some df → df.ino ∈ st.tree)
    (hdisj : ∀ fd, st'.proc.fds !! fd ≠ none → st'.proc.dfds !! fd = none)
    (hflt : ∀ i, i ∈ st'.fs.files → i < st'.fs.nextIno) : FsTreeWf st' := by
  have htree : st'.tree = o.apply st.tree := by
    simp only [OsState.tree, hlog, hdur, List.map_append, List.map_cons, List.map_nil]
    rw [replay_snoc]
  refine ⟨hroots ▸ hw.roots, fun n hn => ?_, fun fd df h => ?_, hdisj, hflt⟩
  · rw [hlog] at hn ⊢; rw [hdur, hroots]
    by_cases hle : n ≤ st.fs.metaLog.length
    · rw [List.take_append_of_le_length hle]
      obtain ⟨h1, h2, h3⟩ := hw.hist n hle
      refine ⟨h1, fun i hi => ?_, fun j hj => Nat.lt_of_lt_of_le (h3 j hj) hnext⟩
      obtain ⟨f, hf⟩ := h2 i hi; exact hfiles i f hf
    · have hn' : n = st.fs.metaLog.length + 1 := by simp at hn; omega
      subst hn'
      rw [List.take_of_length_le (by simp)]
      have : replay ((st.fs.metaLog ++ [(⟨o, s⟩ : LogEntry)]).map (·.op)) st.fs.treeDur =
          o.apply st.tree := by
        simp only [List.map_append, List.map_cons, List.map_nil]; rw [replay_snoc]; rfl
      rw [this]
      exact ⟨htw, hnamed, hlt⟩
  · rw [htree]; exact apply_mem_mono o st.tree _ (hdfds fd df h)

/-- **The coherence after a step that held the whole history** (no directory fd open, no other call
in flight): the history with the entry logged. -/
theorem treeCoh_meta {st st' : OsState} {V : Hist} {Γdf : GMap w64 (Ino × DirPh)}
    {Γc : GMap Nat (Nat × Qp)} (hc : TreeCoh st V Γdf Γc) (hΓdf : Γdf = ∅) {k s : Nat} {q : Qp}
    (hk : Γc !! k = some (s, q)) (hΓc : GMap.delete k Γc = ∅) {o : MetaOp}
    (hlog : st'.fs.metaLog = st.fs.metaLog ++ [⟨o, s⟩]) (hdur : st'.fs.treeDur = st.fs.treeDur)
    (hdfds : st'.proc.dfds = ∅) (hcalls : st'.proc.calls = GMap.delete k st.proc.calls) :
    TreeCoh st' (V.push ⟨o, s⟩) ∅ ∅ := by
  have hs : s = st.fs.metaLog.length := hc.start k _ hk
  refine ⟨?_, ?_, fun fd => ?_, fun fd x df hx => by simp at hx, fun fd x hx => by simp at hx,
    fun t => ?_, fun t x hx => by simp at hx⟩
  · rw [hc.hist, hlog, hdur]; rfl
  · rw [hlog, hs]; exact sequential_snoc hc.seq
  · rw [hdfds]; simp
  · rw [hcalls]
    simp only [GMap.lookup_empty, Option.map_none]
    by_cases ht : k = t
    · subst ht; rw [GMap.lookup_delete_eq]
    · rw [GMap.lookup_delete_ne _ ht, ← hc.calls t]
      have := congrArg (· !! t) hΓc
      simp only [GMap.lookup_delete_ne _ ht, GMap.lookup_empty] at this
      rw [this]; rfl

/-- With no directory fd in the ghost state, none in the state. -/
theorem dfds_empty {st : OsState} {V : Hist} {Γc : GMap Nat (Nat × Qp)}
    (hc : TreeCoh st V ∅ Γc) : st.proc.dfds = ∅ := by
  apply GMap.ext; intro fd
  have := hc.fds fd
  simp only [GMap.lookup_empty, Option.map_none] at this ⊢
  cases h : st.proc.dfds !! fd with
  | none => rfl
  | some df => rw [h] at this; cases this

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-! ## The ghost state of calls -/

theorem osTree_split (q1 q2 : Qp) (R : Roots) (V : Hist) :
    osTree (L := L) (DFrac.own (q1 + q2)) R V ⊣⊢
      osTree (L := L) (DFrac.own q1) R V ∗ osTree (L := L) (DFrac.own q2) R V :=
  gElem_split _ _ () q1 q2 (R, V)

/-- A call ended: its token and its fraction of the history leave the state interpretation, and
the fraction comes back to the caller. -/
theorem call_end (R : Roots) (V : Hist) (Γc : GMap Nat (Nat × Qp)) (k s : Nat) (q : Qp) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (R, V)) -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γc Γc -∗
      callRes (gooseOsGS (L := L)) Γc -∗ osCall (L := L) k s q ==∗
      ⌜Γc !! k = some (s, q)⌝ ∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (R, V)) ∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γc (GMap.delete k Γc) ∗
      callRes (gooseOsGS (L := L)) (GMap.delete k Γc) ∗ osTree (L := L) (DFrac.own q) R V := by
  iintro HAd HAc Hcr Hk
  icases osCall_auth Γc k s q $$ HAc Hk with %hk
  unfold callRes
  icases (BigSepM.bigSepM_delete (Φ := fun (_t : Nat) (x : Nat × Qp) =>
      iprop(∃ RV : Roots × Hist, gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd () (DFrac.own x.2) RV))
      hk).1 $$ Hcr with ⟨⟨%RV, Hq⟩, Hcr⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hq with %hRV
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq] at hRV
  subst hRV
  unfold osCall
  imod gAuth_delete _ _ _ _ _ $$ HAc Hk with HAc
  imodintro
  iframe HAd HAc Hcr
  isplitr
  · ipureintro; exact hk
  unfold osTree; iexact Hq

/-- The holder of the whole history knows that no directory fd is open and no call is in flight. -/
theorem whole_alone (R : Roots) (V : Hist) (Γdf : GMap w64 (Ino × DirPh))
    (Γc : GMap Nat (Nat × Qp)) :
    ⊢ osTree (L := L) (DFrac.own 1) R V -∗ rdRes (gooseOsGS (L := L)) Γdf -∗
      callRes (gooseOsGS (L := L)) Γc -∗
      ⌜Γdf = ∅ ∧ Γc = ∅⌝ ∗ osTree (L := L) (DFrac.own 1) R V ∗
      rdRes (gooseOsGS (L := L)) Γdf ∗ callRes (gooseOsGS (L := L)) Γc := by
  iintro Hd Hrd Hcr
  by_cases h1 : Γdf = ∅
  · by_cases h2 : Γc = ∅
    · iframe; ipureintro; exact ⟨h1, h2⟩
    · have : ∃ t x, Γc !! t = some x := by
        refine Classical.byContradiction fun hn => h2 (GMap.ext fun t => ?_)
        cases h : Γc !! t with
        | none => rfl
        | some x => exact absurd ⟨t, x, h⟩ hn
      obtain ⟨t, x, hx⟩ := this
      unfold callRes
      icases (BigSepM.bigSepM_lookup (Φ := fun (_t : Nat) (x : Nat × Qp) =>
          iprop(∃ RV : Roots × Hist, gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd () (DFrac.own x.2) RV))
          hx) $$ Hcr with ⟨%RV, Hq⟩
      unfold osTree
      icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hd Hq with %Hv
      exact absurd (DFrac.valid_own_op Hv.1) (by simp)
  · have : ∃ fd x, Γdf !! fd = some x := by
      refine Classical.byContradiction fun hn => h1 (GMap.ext fun t => ?_)
      cases h : Γdf !! t with
      | none => rfl
      | some x => exact absurd ⟨t, x, h⟩ hn
    obtain ⟨fd, x, hx⟩ := this
    unfold rdRes
    icases (BigSepM.bigSepM_lookup (Φ := fun (_ : w64) (x : Ino × DirPh) =>
        rdPart (gooseOsGS (L := L)) x) hx) $$ Hrd with Hq
    unfold rdPart osTree
    icases Hq with ⟨%RV, Hq, -⟩
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hd Hq with %Hv
    exact absurd (DFrac.valid_own_op Hv.1) (by simp)

/-! ## `CallBegin` -/

/-- **`CallBegin()`**, with a fraction `q1 + q2` of the history: a call in flight, holding `q2` of
it, begun when the log had `V`'s length. -/
theorem wp_osCallBegin (R : Roots) (V : Hist) (q1 q2 : Qp) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own (q1 + q2)) R V -∗
      (∀ t : Nat, osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) t V.2.length q2 -∗
        Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "CallBegin" (Val (#()))) @ s; E {{ Φ }} := by
  iintro #Hinv Hh HΦ
  iapply wp_fs_stepT "CallBegin" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %V0 %Γdf %Γc %h Hw Hn
  unfold osWorld treeWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  obtain ⟨t, ht1, ht2⟩ := exists_fresh2 st.proc.calls st.proc.inflight
  have hs : FilesSame st (st.setProc { st.proc with
      calls := <[t := st.fs.metaLog.length]> st.proc.calls }) := ⟨rfl, rfl, rfl, rfl⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs Hag
    exact ⟨_, h, _, ⟨t, rfl, ht1, ht2, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨t', -, h1', h2', rfl, rfl⟩ := Hst
  imod osWorld_filesSame (st := st)
    (st' := st.setProc { st.proc with calls := <[t' := st.fs.metaLog.length]> st.proc.calls })
    ⟨rfl, rfl, rfl, rfl⟩ Hr Hfr $$ [HAb HAm HAf HAt Htok Hcells Hσ]
    with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh⟩
  have hΓc : Γc !! t' = none := by
    have := hc.calls t'; rw [h1'] at this
    cases h0 : Γc !! t' with
    | none => rfl
    | some x => rw [h0] at this; cases this
  imod gAuth_insert _ _ _ _ ((st.fs.metaLog.length, q2) : Nat × Qp) hΓc $$ HAc with ⟨HAc, Hk⟩
  icases (osTree_split q1 q2 _ _).1 $$ Hh with ⟨H1, H2⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, V, Γdf,
    <[t' := ((st.fs.metaLog.length, q2) : Nat × Qp)]> Γc
  dsimp only
  unfold osWorld
  isplitl [Hw]
  · iexact Hw
  simp only [OsState.setProc]
  iframe HAd HAdf HAc Hrd
  isplitl [H2 Hcr]
  · isplitr
    · ipureintro
      refine ⟨⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩,
        ⟨hc.hist, hc.seq, hc.fds, hc.ph, hc.rd, fun t0 => ?_, fun t0 x hx => ?_⟩⟩
      · show _ = (<[t' := st.fs.metaLog.length]> st.proc.calls) !! t0
        by_cases h0 : t' = t0
        · subst h0; simp
        · rw [GMap.lookup_insert_ne _ _ h0, GMap.lookup_insert_ne _ _ h0]; exact hc.calls t0
      · by_cases h0 : t' = t0
        · subst h0; rw [GMap.lookup_insert] at hx; cases hx; rfl
        · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact hc.start t0 x hx
    · unfold callRes
      iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (x : Nat × Qp) =>
        iprop(∃ RV : Roots × Hist, gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd () (DFrac.own x.2) RV))
        hΓc).2
      iframe Hcr
      iexists (st.fs.roots, V)
      unfold osTree; iexact H2
  iapply wp_value'
  iapply HΦ $$ %t' H1
  have hl : V.2.length = st.fs.metaLog.length := by rw [hc.hist]
  unfold osCall; rw [hl]; iexact Hk

end specs

end Fs
end Perennial

end
