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
