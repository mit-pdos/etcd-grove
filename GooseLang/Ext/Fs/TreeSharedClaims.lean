/-
The shared mode of the tree: claims split, merged and re-keyed (`osNames_split'`, `osNames_merge'`,
`osNames_rekey'`), with the pure facts they rest on: a claim's history restricted to fewer names is
the history of those names (`namesOf_restrict`), and the claims' coherence with some names of one
directory unclaimed (`CohEx`). `TreeShared.lean` states the laws and takes their proofs from here.
Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedLaws

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Name sets -/

theorem NameSet.mem_inter (N : NameSet) (M : List GoString) (b : GoString) :
    (N.inter M).Mem b ↔ N.Mem b ∧ b ∈ M := by
  cases N <;> simp [NameSet.inter, NameSet.Mem, and_comm]

theorem NameSet.mem_diff (N : NameSet) (M : List GoString) (b : GoString) :
    (N.diff M).Mem b ↔ N.Mem b ∧ b ∉ M := by
  cases N <;> simp [NameSet.diff, NameSet.Mem, not_or]

/-- The only key with no name is `.only []`. -/
theorem NameSet.eq_empty {N : NameSet} (h : ∀ b, ¬ N.Mem b) : N = .only [] := by
  cases N with
  | only bs =>
    cases bs with
    | nil => rfl
    | cons b bs => exact absurd (by simp [NameSet.Mem]) (h b)
  | except bs =>
    exfalso
    -- a name longer than every name of `bs` is not in `bs`
    let n := (bs.map List.length).sum + 1
    have hn : List.replicate n (0 : w8) ∉ bs := by
      intro hm
      have hle : ∀ (l : List GoString), ∀ c ∈ l, c.length ≤ (l.map List.length).sum := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          intro c hc
          simp only [List.mem_cons] at hc
          simp only [List.map_cons, List.sum_cons]
          rcases hc with rfl | hc
          · omega
          · have := ih c hc; omega
      have h1 := hle bs _ hm
      simp only [List.length_replicate, n] at h1; omega
    exact h _ hn

/-! ## Histories restricted -/

open Classical in
theorem restrictN_restrictN (N M : NameSet) (e : Ents) (hMN : ∀ b, M.Mem b → N.Mem b) :
    restrictN M (restrictN N e) = restrictN M e := by
  ext b
  unfold restrictN
  simp only [GMap.lookup_filter]
  cases e.lookup b <;> simp only [Option.filter_none, Option.filter_some]
  by_cases hm : M.Mem b
  · simp [hm, hMN b hm]
  · simp [hm]

theorem restrictN_congr {N N' : NameSet} (h : N.Same N') (e : Ents) : restrictN N e = restrictN N' e := by
  ext b
  unfold restrictN
  simp only [GMap.lookup_filter]
  cases e.lookup b <;> simp [h b]

open Classical in
/-- A claim's history restricted to fewer names: those names' history. -/
theorem namesOf_restrict (V : Hist) (j : Ino) (N M : NameSet) (hMN : ∀ b, M.Mem b → N.Mem b) :
    (namesOf V j N).restrict j M = namesOf V j M := by
  have hb : (namesOf V j N).restrict j M = ⟨(namesOf V j M).boot, ((namesOf V j N).restrict j M).ents,
      (namesOf V j M).cur⟩ := by
    unfold NamesH.restrict namesOf
    simp only [restrictN_restrictN N M _ hMN]
  rw [hb]
  have he : ((namesOf V j N).restrict j M).ents = (namesOf V j M).ents := by
    unfold NamesH.restrict
    simp only
    rw [namesOf_ents, namesOf_ents, List.filter_map, List.map_map, List.filter_filter]
    have hf : ∀ x ∈ List.range V.2.length,
        (((fun xe : Nat × LogEntry × Ents => decide (∃ b, M.Mem b ∧ xe.2.1.op.Writes j b)) ∘
          (fun x => (x, (V.2[x]?).getD ⟨.create 0 [] 0, 0⟩,
            restrictN N (entsOf (prefTree V.1 V.2 (x + 1)) j)))) x &&
          decide (∃ e, V.2[x]? = some e ∧ ∃ b, N.Mem b ∧ e.op.Writes j b)) =
        decide (∃ e, V.2[x]? = some e ∧ ∃ b, M.Mem b ∧ e.op.Writes j b) := by
      intro x hx
      have hxL : x < V.2.length := List.mem_range.1 hx
      simp only [Function.comp, List.getElem?_eq_getElem hxL, Option.getD_some, Option.some.injEq,
        exists_eq_left']
      by_cases h1 : ∃ b, M.Mem b ∧ V.2[x].op.Writes j b
      · obtain ⟨b, hb1, hb2⟩ := h1
        have h2 : ∃ b, N.Mem b ∧ V.2[x].op.Writes j b := ⟨b, hMN b hb1, hb2⟩
        have h3 : ∃ b, M.Mem b ∧ V.2[x].op.Writes j b := ⟨b, hb1, hb2⟩
        simp only [decide_eq_true h3, decide_eq_true h2, Bool.and_self]
      · simp [h1]
    rw [List.filter_congr hf]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp, restrictN_restrictN N M _ hMN]
  rw [he]

theorem namesOf_restrict_self (V : Hist) (j : Ino) (N : NameSet) :
    (namesOf V j N).restrict j N = namesOf V j N :=
  namesOf_restrict V j N N (fun _ h => h)

open Classical in
theorem namesOf_congr (V : Hist) (j : Ino) {N N' : NameSet} (h : N.Same N') :
    namesOf V j N = namesOf V j N' := by
  have hm : N.Mem = N'.Mem := funext fun b => propext (h b)
  unfold namesOf
  simp only [restrictN_congr h, hm]

/-! ### `next` of a history -/

/-- One past the last index below `n` satisfying `P`, `0` if none. -/
def lastSat (n : Nat) (P : Nat → Bool) : Nat :=
  (((List.range n).filter P).getLast?.map (· + 1)).getD 0

theorem lastSat_succ (n : Nat) (P : Nat → Bool) :
    lastSat (n + 1) P = if P n then n + 1 else lastSat n P := by
  unfold lastSat
  rw [List.range_succ, List.filter_append]
  by_cases h : P n
  · simp [h]
  · simp [h]

theorem lastSat_or (n : Nat) (P Q : Nat → Bool) :
    lastSat n (fun x => P x || Q x) = max (lastSat n P) (lastSat n Q) := by
  induction n with
  | zero => simp [lastSat]
  | succ n ih =>
    rw [lastSat_succ, lastSat_succ, lastSat_succ, ih]
    have hP : lastSat n P ≤ n := by
      unfold lastSat
      cases hl : ((List.range n).filter P).getLast? with
      | none => simp
      | some x =>
        have := List.mem_range.1 (List.mem_filter.1 (List.mem_of_getLast? hl)).1
        simp; omega
    have hQ : lastSat n Q ≤ n := by
      unfold lastSat
      cases hl : ((List.range n).filter Q).getLast? with
      | none => simp
      | some x =>
        have := List.mem_range.1 (List.mem_filter.1 (List.mem_of_getLast? hl)).1
        simp; omega
    cases hp : P n <;> cases hq : Q n <;> simp <;> omega

open Classical in
theorem namesOf_next (V : Hist) (j : Ino) (N : NameSet) :
    (namesOf V j N).next = lastSat V.2.length (fun x => decide
        (∃ e, V.2[x]? = some e ∧ ∃ b, N.Mem b ∧ e.op.Writes j b)) := by
  unfold NamesH.next lastSat
  rw [namesOf_ents, List.getLast?_map, Option.map_map]
  rfl

open Classical in
theorem namesOf_next_union (V : Hist) (j : Ino) (N N' N'' : NameSet)
    (hN : ∀ b, N''.Mem b ↔ N.Mem b ∨ N'.Mem b) :
    (namesOf V j N'').next = max (namesOf V j N).next (namesOf V j N').next := by
  rw [namesOf_next, namesOf_next, namesOf_next, ← lastSat_or]
  unfold lastSat
  congr 3
  apply List.filter_congr
  intro x _
  rw [← Bool.decide_or]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨e, he, b, hb, hw⟩
    rcases (hN b).1 hb with hb | hb
    · exact Or.inl ⟨e, he, b, hb, hw⟩
    · exact Or.inr ⟨e, he, b, hb, hw⟩
  · rintro (⟨e, he, b, hb, hw⟩ | ⟨e, he, b, hb, hw⟩)
    · exact ⟨e, he, b, (hN b).2 (Or.inl hb), hw⟩
    · exact ⟨e, he, b, (hN b).2 (Or.inr hb), hw⟩

/-! ## The claims' coherence with some names of a directory unclaimed -/

/-- `NamesCoh`, but the names `U` of the directory `j` need not be claimed, and no claim of `j`
has one of them. -/
structure CohEx (V : Hist) (Γn : GMap (Ino × NameSet) NamesH) (j : Ino) (U : GoString → Prop) :
    Prop where
  hist : ∀ j N h, Γn !! (j, N) = some h → h = namesOf V j N
  disj : ∀ j N N' h h' b, Γn !! (j, N) = some h → Γn !! (j, N') = some h' → N ≠ N' →
    N.Mem b → ¬ N'.Mem b
  cover : ∀ j' b, j' ∈ V.now → ¬ (j' = j ∧ U b) → ∃ N h, Γn !! (j', N) = some h ∧ N.Mem b
  free : ∀ N h b, Γn !! (j, N) = some h → N.Mem b → ¬ U b
  dirs : ∀ j N h, Γn !! (j, N) = some h → j ∈ V.now
  udir : ∀ b, U b → j ∈ V.now

theorem CohEx.of_coh {V : Hist} {Γn : GMap (Ino × NameSet) NamesH} (h : NamesCoh V Γn) (j : Ino) :
    CohEx V Γn j (fun _ => False) :=
  ⟨h.hist, h.disj, fun j' b hj _ => h.cover j' b hj, fun _ _ _ _ _ h => h, h.dirs,
    fun _ h => h.elim⟩

theorem CohEx.coh {V : Hist} {Γn : GMap (Ino × NameSet) NamesH} {j : Ino} {U : GoString → Prop}
    (h : CohEx V Γn j U) (hU : ∀ b, ¬ U b) : NamesCoh V Γn :=
  ⟨h.hist, h.disj, fun j' b hj => h.cover j' b hj (fun hh => hU b hh.2), h.dirs⟩

theorem CohEx.iff {V : Hist} {Γn : GMap (Ino × NameSet) NamesH} {j : Ino} {U U' : GoString → Prop}
    (h : CohEx V Γn j U) (hU : ∀ b, U b ↔ U' b) : CohEx V Γn j U' :=
  ⟨h.hist, h.disj, fun j' b hj hn => h.cover j' b hj (fun hh => hn ⟨hh.1, (hU b).1 hh.2⟩),
    fun N hh b hl hm hu => h.free N hh b hl hm ((hU b).2 hu), h.dirs,
    fun b hu => h.udir b ((hU b).2 hu)⟩

theorem CohEx.del {V : Hist} {Γn : GMap (Ino × NameSet) NamesH} {j : Ino} {U : GoString → Prop}
    (hc : CohEx V Γn j U) {N : NameSet} {h : NamesH} (hl : Γn !! (j, N) = some h) :
    CohEx V (GMap.delete (j, N) Γn) j (fun b => U b ∨ N.Mem b) where
  hist := by
    intro j1 N1 h1 hl1
    rw [GMap.lookup_delete_iff] at hl1
    split at hl1
    · cases hl1
    · exact hc.hist _ _ _ hl1
  disj := by
    intro j1 N1 N2 h1 h2 b hl1 hl2
    rw [GMap.lookup_delete_iff] at hl1 hl2
    split at hl1
    · cases hl1
    split at hl2
    · cases hl2
    exact hc.disj _ _ _ _ _ _ hl1 hl2
  cover := by
    intro j1 b hj hn
    obtain ⟨N1, h1, hl1, hm⟩ := hc.cover j1 b hj (fun hh => hn ⟨hh.1, Or.inl hh.2⟩)
    refine ⟨N1, h1, ?_, hm⟩
    rw [GMap.lookup_delete_ne]
    · exact hl1
    · intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hn ⟨rfl, Or.inr hm⟩
  free := by
    intro N1 h1 b hl1 hm hu
    rw [GMap.lookup_delete_iff] at hl1
    split at hl1
    · cases hl1
    rename_i hne
    rcases hu with hu | hu
    · exact hc.free _ _ _ hl1 hm hu
    · have hNN : N1 ≠ N := fun he => hne (by rw [he])
      exact hc.disj _ _ _ _ _ b hl1 hl hNN hm hu
  dirs := by
    intro j1 N1 h1 hl1
    rw [GMap.lookup_delete_iff] at hl1
    split at hl1
    · cases hl1
    · exact hc.dirs _ _ _ hl1
  udir := by
    rintro b (hu | _)
    · exact hc.udir b hu
    · exact hc.dirs _ _ _ hl

theorem CohEx.ins {V : Hist} {Γn : GMap (Ino × NameSet) NamesH} {j : Ino} {U : GoString → Prop}
    (hc : CohEx V Γn j U) {N : NameSet} (hNU : ∀ b, N.Mem b → U b) (hne : N ≠ .only []) :
    Γn !! (j, N) = none ∧
    CohEx V (<[(j, N) := namesOf V j N]> Γn) j (fun b => U b ∧ ¬ N.Mem b) := by
  have hb : ∃ b, N.Mem b := Classical.byContradiction fun hn =>
    hne (NameSet.eq_empty (fun b hb => hn ⟨b, hb⟩))
  obtain ⟨b0, hb0⟩ := hb
  have hfree : Γn !! (j, N) = none := by
    cases hl : Γn !! (j, N) with
    | none => rfl
    | some h => exact absurd (hNU b0 hb0) (hc.free N h b0 hl hb0)
  refine ⟨hfree, ?_, ?_, ?_, ?_, ?_, fun b hu => hc.udir b hu.1⟩
  · intro j1 N1 h1 hl1
    rw [GMap.lookup_insert_eq_iff] at hl1
    split at hl1
    · rename_i he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      cases hl1; rfl
    · exact hc.hist _ _ _ hl1
  · intro j1 N1 N2 h1 h2 b hl1 hl2 hne12 hm1 hm2
    rw [GMap.lookup_insert_eq_iff] at hl1 hl2
    split at hl1 <;> split at hl2
    · rename_i he1 he2
      simp only [Prod.mk.injEq] at he1 he2
      exact hne12 (he1.2.symm.trans he2.2)
    · rename_i he1 _
      simp only [Prod.mk.injEq] at he1
      obtain ⟨rfl, rfl⟩ := he1
      exact hc.free _ _ _ hl2 hm2 (hNU b hm1)
    · rename_i he2
      simp only [Prod.mk.injEq] at he2
      obtain ⟨rfl, rfl⟩ := he2
      exact hc.free _ _ _ hl1 hm1 (hNU b hm2)
    · exact hc.disj _ _ _ _ _ _ hl1 hl2 hne12 hm1 hm2
  · intro j1 b hj hn
    by_cases hc1 : j1 = j ∧ U b
    · obtain ⟨rfl, hu⟩ := hc1
      have hm : N.Mem b := Classical.byContradiction fun hm => hn ⟨rfl, hu, hm⟩
      exact ⟨N, _, GMap.lookup_insert _ _ _, hm⟩
    · obtain ⟨N1, h1, hl1, hm⟩ := hc.cover j1 b hj hc1
      refine ⟨N1, h1, ?_, hm⟩
      rw [GMap.lookup_insert_ne]
      · exact hl1
      · intro he
        rw [he] at hfree; rw [hfree] at hl1; cases hl1
  · intro N1 h1 b hl1 hm hu
    rw [GMap.lookup_insert_eq_iff] at hl1
    split at hl1
    · rename_i he
      simp only [Prod.mk.injEq] at he
      rw [← he.2] at hm
      exact hu.2 hm
    · exact hc.free _ _ _ hl1 hm hu.1
  · intro j1 N1 h1 hl1
    rw [GMap.lookup_insert_eq_iff] at hl1
    split at hl1
    · rename_i he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hc.udir b0 (hNU b0 hb0)
    · exact hc.dirs _ _ _ hl1

/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {E : CoPset}

theorem osNames_frac (j : Ino) (N : NameSet) (q1 q2 : Qp) (h : NamesH) :
    osNames (L := L) j N (DFrac.own (q1 + q2)) h ⊣⊢
      osNames (L := L) j N (DFrac.own q1) h ∗ osNames (L := L) j N (DFrac.own q2) h := by
  by_cases hN : N = .only []
  · subst hN
    unfold osNames
    simp only [if_pos]
    constructor
    · iintro %H; isplitl [] <;> ipureintro <;> exact H
    · iintro ⟨%H, -⟩; ipureintro; exact H
  · rw [osNames_of_ne _ _ hN, osNames_of_ne _ _ hN, osNames_of_ne _ _ hN]
    exact gElem_split _ _ _ q1 q2 h

theorem osNames_agree (j : Ino) (N : NameSet) (dq1 dq2 : DFrac) (h1 h2 : NamesH) :
    osNames (L := L) j N dq1 h1 -∗ osNames (L := L) j N dq2 h2 -∗ ⌜h1 = h2⌝ := by
  by_cases hN : N = .only []
  · subst hN
    unfold osNames
    simp only [if_pos]
    iintro %H1 %H2
    ipureintro; rw [H1, H2]
  · rw [osNames_of_ne _ _ hN, osNames_of_ne _ _ hN]
    iintro H1 H2
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %hv
    ipureintro; exact hv.2

/-- A whole claim given back to the authority: its names unclaimed. -/
theorem osNames_del {V : Hist} {Γn : GMap (Ino × NameSet) NamesH} {j : Ino} {U : GoString → Prop}
    (hc : CohEx V Γn j U) (N : NameSet) (h : NamesH) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗
      osNames (L := L) j N (DFrac.own 1) h ==∗
      ∃ Γ', ⌜CohEx V Γ' j (fun b => U b ∨ N.Mem b) ∧ h = namesOf V j N⌝ ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γ' := by
  iintro HA H
  by_cases hN : N = .only []
  · subst hN
    unfold osNames
    rw [if_pos rfl]
    icases H with %h1
    imodintro
    iexists Γn
    iframe HA
    ipureintro
    refine ⟨hc.iff (fun b => by simp [NameSet.Mem]), ?_⟩
    rw [h1, namesOf_empty]
  · rw [osNames_of_ne _ _ hN]
    icases gAuth_lookup _ _ _ _ _ _ $$ HA H with %hl
    imod gAuth_delete _ _ _ _ _ $$ HA H with HA
    imodintro
    iexists _
    iframe HA
    ipureintro
    exact ⟨hc.del hl, hc.hist _ _ _ hl⟩

/-- An unclaimed set of names claimed, whole. -/
theorem osNames_ins {V : Hist} {Γn : GMap (Ino × NameSet) NamesH} {j : Ino} {U : GoString → Prop}
    (hc : CohEx V Γn j U) (N : NameSet) (hNU : ∀ b, N.Mem b → U b) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ==∗
      ∃ Γ', ⌜CohEx V Γ' j (fun b => U b ∧ ¬ N.Mem b)⌝ ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γ' ∗
        osNames (L := L) j N (DFrac.own 1) (namesOf V j N) := by
  iintro HA
  by_cases hN : N = .only []
  · subst hN
    imodintro
    iexists Γn
    iframe HA
    unfold osNames
    rw [if_pos rfl]
    isplitl []
    · ipureintro; exact hc.iff (fun b => by simp [NameSet.Mem])
    · ipureintro; exact namesOf_empty V j
  · obtain ⟨hfree, hc'⟩ := hc.ins hNU hN
    imod gAuth_insert _ _ _ _ (namesOf V j N) hfree $$ HA with ⟨HA, H⟩
    imodintro
    iexists _
    iframe HA
    rw [osNames_of_ne _ _ hN]
    isplitl []
    · ipureintro; exact hc'
    · iexact H

theorem osNames_split' (R : Roots) (j : Ino) (N : NameSet) (M : List GoString) (h : NamesH)
    (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R -∗ osNames (L := L) j N (DFrac.own 1) h ={E}=∗
      osNames (L := L) j (N.inter M) (DFrac.own 1) (h.restrict j (N.inter M)) ∗
      osNames (L := L) j (N.diff M) (DFrac.own 1) (h.restrict j (N.diff M)) := by
  unfold osSharedInv
  iintro #Hsi H
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  imod osNames_del (CohEx.of_coh hcoh.2 j) N h $$ HAn H with ⟨%Γ1, %hc1, HAn⟩
  obtain ⟨hc1, rfl⟩ := hc1
  imod osNames_ins hc1 (N.inter M) (fun b hb => Or.inr ((N.mem_inter M b).1 hb).1) $$ HAn
    with ⟨%Γ2, %hc2, HAn, H1⟩
  imod osNames_ins hc2 (N.diff M) (fun b hb => ⟨Or.inr ((N.mem_diff M b).1 hb).1,
      fun hi => ((N.mem_diff M b).1 hb).2 ((N.mem_inter M b).1 hi).2⟩) $$ HAn
    with ⟨%Γ3, %hc3, HAn, H2⟩
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γ3; iframe; ipureintro
    refine ⟨hcoh.1, hc3.coh ?_⟩
    rintro b ⟨⟨hu | hu, hi⟩, hd⟩
    · exact hu
    · by_cases hbM : b ∈ M
      · exact hi ((N.mem_inter M b).2 ⟨hu, hbM⟩)
      · exact hd ((N.mem_diff M b).2 ⟨hu, hbM⟩)
  imodintro
  rw [namesOf_restrict Vs j N (N.inter M) (fun b hb => ((N.mem_inter M b).1 hb).1),
    namesOf_restrict Vs j N (N.diff M) (fun b hb => ((N.mem_diff M b).1 hb).1)]
  iframe

theorem osNames_merge' (R : Roots) (j : Ino) (N N' N'' : NameSet) (h h' : NamesH)
    (hN : ∀ b, N''.Mem b ↔ N.Mem b ∨ N'.Mem b) (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R -∗ osNames (L := L) j N (DFrac.own 1) h -∗
      osNames (L := L) j N' (DFrac.own 1) h' ={E}=∗
      ∃ h'', osNames (L := L) j N'' (DFrac.own 1) h'' ∗
        ⌜h''.restrict j N = h.restrict j N ∧ h''.restrict j N' = h'.restrict j N' ∧
          h''.next = max h.next h'.next⌝ := by
  unfold osSharedInv
  iintro #Hsi H H'
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  imod osNames_del (CohEx.of_coh hcoh.2 j) N h $$ HAn H with ⟨%Γ1, %hc1, HAn⟩
  obtain ⟨hc1, rfl⟩ := hc1
  imod osNames_del hc1 N' h' $$ HAn H' with ⟨%Γ2, %hc2, HAn⟩
  obtain ⟨hc2, rfl⟩ := hc2
  imod osNames_ins hc2 N'' (fun b hb => by
      rcases (hN b).1 hb with h1 | h1
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1) $$ HAn
    with ⟨%Γ3, %hc3, HAn, H''⟩
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γ3; iframe; ipureintro
    refine ⟨hcoh.1, hc3.coh ?_⟩
    rintro b ⟨(hu | hu) | hu, hn⟩
    · exact hu
    · exact hn ((hN b).2 (Or.inl hu))
    · exact hn ((hN b).2 (Or.inr hu))
  imodintro
  iexists _
  iframe H''
  ipureintro
  refine ⟨?_, ?_, namesOf_next_union Vs j N N' N'' hN⟩
  · rw [namesOf_restrict Vs j N'' N (fun b hb => (hN b).2 (Or.inl hb)), namesOf_restrict_self]
  · rw [namesOf_restrict Vs j N'' N' (fun b hb => (hN b).2 (Or.inr hb)), namesOf_restrict_self]

theorem osNames_rekey' (R : Roots) (j : Ino) (N N' : NameSet) (h : NamesH) (hN : N.Same N')
    (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R -∗ osNames (L := L) j N (DFrac.own 1) h ={E}=∗
      osNames (L := L) j N' (DFrac.own 1) h := by
  unfold osSharedInv
  iintro #Hsi H
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  imod osNames_del (CohEx.of_coh hcoh.2 j) N h $$ HAn H with ⟨%Γ1, %hc1, HAn⟩
  obtain ⟨hc1, rfl⟩ := hc1
  imod osNames_ins hc1 N' (fun b hb => Or.inr ((hN b).2 hb)) $$ HAn with ⟨%Γ2, %hc2, HAn, H'⟩
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γ2; iframe; ipureintro
    refine ⟨hcoh.1, hc2.coh ?_⟩
    rintro b ⟨hu | hu, hn⟩
    · exact hu
    · exact hn ((hN b).1 hu)
  imodintro
  rw [namesOf_congr Vs j hN]
  iexact H'

/-! ### Spines and paths -/

theorem osSpine_nil (j : Ino) (dq : DFrac) (j' : Ino) :
    osSpine (L := L) j [] dq j' = iprop(⌜j = j'⌝) := by simp only [osSpine]

theorem osSpine_cons (j : Ino) (c : GoString) (cs : List GoString) (dq : DFrac) (j' : Ino) :
    osSpine (L := L) j (c :: cs) dq j' = iprop(∃ (h : NamesH) (J : Ino),
      osNames (L := L) j (.only [c]) dq h ∗ ⌜h.cur !! c = some (.dir J)⌝ ∗
        osSpine (L := L) J cs dq j') := by simp only [osSpine]

theorem osSpine_frac (cs : List GoString) (j : Ino) (q1 q2 : Qp) (j' : Ino) :
    osSpine (L := L) j cs (DFrac.own (q1 + q2)) j' ⊢
      osSpine (L := L) j cs (DFrac.own q1) j' ∗ osSpine (L := L) j cs (DFrac.own q2) j' := by
  induction cs generalizing j with
  | nil =>
    rw [osSpine_nil, osSpine_nil, osSpine_nil]
    iintro %h; isplitl [] <;> ipureintro <;> exact h
  | cons c cs ih =>
    rw [osSpine_cons, osSpine_cons, osSpine_cons]
    iintro ⟨%h, %J, Hn, %hJ, Hs⟩
    icases (osNames_frac (L := L) j (.only [c]) q1 q2 h).1 $$ Hn with ⟨Hn1, Hn2⟩
    icases ih J $$ Hs with ⟨Hs1, Hs2⟩
    isplitl [Hn1 Hs1]
    · iexists h, J; iframe; ipureintro; exact hJ
    · iexists h, J; iframe; ipureintro; exact hJ

theorem osSpine_join (cs : List GoString) (j : Ino) (q1 q2 : Qp) (j1 j2 : Ino) :
    osSpine (L := L) j cs (DFrac.own q1) j1 ∗ osSpine (L := L) j cs (DFrac.own q2) j2 ⊢
      ⌜j1 = j2⌝ ∗ osSpine (L := L) j cs (DFrac.own (q1 + q2)) j1 := by
  induction cs generalizing j with
  | nil =>
    rw [osSpine_nil, osSpine_nil, osSpine_nil]
    iintro ⟨%h1, %h2⟩; isplitl [] <;> ipureintro
    · exact h1.symm.trans h2
    · exact h1
  | cons c cs ih =>
    rw [osSpine_cons, osSpine_cons, osSpine_cons]
    iintro ⟨⟨%h1, %J1, Hn1, %hJ1, Hs1⟩, ⟨%h2, %J2, Hn2, %hJ2, Hs2⟩⟩
    icases osNames_agree (L := L) _ _ _ _ _ _ $$ Hn1 Hn2 with %he
    subst he
    have hJ : J1 = J2 := by rw [hJ1] at hJ2; cases hJ2; rfl
    subst hJ
    icases ih J1 $$ [Hs1 Hs2] with ⟨%hj, Hs⟩
    · isplitl [Hs1]; iexact Hs1; iexact Hs2
    isplitl []
    · ipureintro; exact hj
    iexists h1, J1
    iframe Hs
    isplitl [Hn1 Hn2]
    · iapply (osNames_frac (L := L) j (.only [c]) q1 q2 h1).2; isplitl [Hn1]; iexact Hn1; iexact Hn2
    · ipureintro; exact hJ1

theorem osSpine_snoc (cs : List GoString) (j : Ino) (dq : DFrac) (j' : Ino) (b : GoString)
    (h : NamesH) (J : Ino) (hJ : h.cur !! b = some (.dir J)) :
    osSpine (L := L) j cs dq j' -∗ osNames (L := L) j' (.only [b]) dq h -∗
      osSpine (L := L) j (cs ++ [b]) dq J := by
  induction cs generalizing j with
  | nil =>
    rw [osSpine_nil, List.nil_append, osSpine_cons]
    iintro %hj Hn
    subst hj
    iexists h, J; rw [osSpine_nil]; iframe; isplit <;> ipureintro
    · exact hJ
    · rfl
  | cons c cs ih =>
    rw [osSpine_cons, List.cons_append, osSpine_cons]
    iintro ⟨%h1, %J1, Hn1, %hJ1, Hs⟩ Hn
    iexists h1, J1
    iframe Hn1
    isplitl []
    · ipureintro; exact hJ1
    iapply ih J1 $$ Hs Hn

theorem osPathS_rootsOk (R : Roots) (p : GoString) (dq : DFrac) (j : Ino) :
    osPathS (L := L) R p dq j ⊢ ⌜RootsOk R⌝ := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %hp, -⟩
  ipureintro; exact hp.1

theorem osPathS_frac' (R : Roots) (p : GoString) (q1 q2 : Qp) (j : Ino) :
    osPathS (L := L) R p (DFrac.own (q1 + q2)) j ⊣⊢
      osPathS (L := L) R p (DFrac.own q1) j ∗ osPathS (L := L) R p (DFrac.own q2) j := by
  unfold osPathS
  constructor
  · iintro ⟨%r, %j0, %cs, %hp, Hs⟩
    icases osSpine_frac (L := L) cs j0 q1 q2 j $$ Hs with ⟨Hs1, Hs2⟩
    isplitl [Hs1]
    · iexists r, j0, cs; iframe; ipureintro; exact hp
    · iexists r, j0, cs; iframe; ipureintro; exact hp
  · iintro ⟨⟨%r, %j0, %cs, %hp, Hs1⟩, ⟨%r', %j0', %cs', %hp', Hs2⟩⟩
    obtain ⟨hR, hm, hcs, rfl⟩ := hp
    obtain ⟨-, hm', hcs', hpe⟩ := hp'
    obtain ⟨he, rfl⟩ := root_split_unique hR hm hm' hcs hcs' hpe
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    icases osSpine_join (L := L) cs j0 q1 q2 j j $$ [Hs1 Hs2] with ⟨-, Hs⟩
    · isplitl [Hs1]; iexact Hs1; iexact Hs2
    iexists r, j0, cs; iframe; ipureintro; exact ⟨hR, hm, hcs, rfl⟩

theorem osPathS_child' (R : Roots) (d b : GoString) (dq : DFrac) (j J : Ino) (h : NamesH)
    (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    osPathS (L := L) R d dq j -∗ osNames (L := L) j (.only [b]) dq h -∗
      osPathS (L := L) R (child d b) dq J := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %hp, Hs⟩ Hn
  obtain ⟨hR, hm, hcs, rfl⟩ := hp
  iexists r, j0, cs ++ [b]
  isplitl []
  · ipureintro
    refine ⟨hR, hm, ?_, (joinPath_snoc r cs b).symm⟩
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hcs c hc
    · exact hb
  iapply osSpine_snoc (L := L) cs j0 dq j b h J hJ $$ Hs Hn

/-- A root of the shared invariant's roots is a path to its directory, held by no claim. -/
theorem osPathS_root' (R : Roots) (r : GoString) (j0 : Ino) (dq : DFrac) (hr : (r, j0) ∈ R)
    (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R ={E}=∗ osPathS (L := L) R r dq j0 := by
  unfold osSharedInv
  iintro #Hsi
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γn; iframe; ipureintro; exact hcoh
  imodintro
  unfold osPathS
  iexists r, j0, []
  rw [osSpine_nil]
  isplitl [] <;> ipureintro
  · exact ⟨hcoh.1, hr, by simp, by simp [joinPath]⟩
  · rfl

end laws

end Fs
end Perennial

end
