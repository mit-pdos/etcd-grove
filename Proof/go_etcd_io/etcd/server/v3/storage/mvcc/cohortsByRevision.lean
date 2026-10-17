/-
Proof of `Spec/.../mvcc/cohortsByRevision.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.cohortsByRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__add
public import Spec.sort.Slice

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The sort key: a member's `minRev`. -/
def mvcc.cohortKey (ST : GMap Loc mvcc.WatcherSt) (w : Loc) : Int :=
  match ST !! w with
  | some st => sint.Z st.minRev
  | none => 0

/-- A member kept by `cohortsByRevision`'s first loop: not behind the compaction revision. -/
def mvcc.cohortKeep (ST : GMap Loc mvcc.WatcherSt) (cr : w64) (w : Loc) : Bool :=
  match ST !! w with
  | some st => decide (sint.Z cr ≤ sint.Z st.minRev)
  | none => false

/-- The second loop's invariant: the cohorts `L` of the members `P` grouped so far (a prefix of
the sorted list). -/
structure mvcc.CohortsPre (W : GMap Loc mvcc.WatchRange) (ST : GMap Loc mvcc.WatcherSt)
    (P : List Loc) (L : List mvcc.Cohort) : Prop where
  sub : ∀ c ∈ L, ∀ w r, c.W !! w = some r → W !! w = some r ∧ w ∈ P
  disj : L.Pairwise (fun c d => ∀ w, (c.W !! w).isSome → d.W !! w = none)
  cover : ∀ w ∈ P, ∃ c ∈ L, (c.W !! w).isSome
  window : ∀ c ∈ L, ∀ w st, (c.W !! w).isSome → ST !! w = some st →
    sint.Z c.minRev ≤ sint.Z st.minRev ∧ sint.Z st.minRev ≤ sint.Z c.minRev + 1000
  anchor : ∀ c ∈ L, ∃ w st, w ∈ P ∧ (c.W !! w).isSome ∧ ST !! w = some st ∧ st.minRev = c.minRev
  sorted : L.Pairwise (fun c d => sint.Z c.minRev + 1000 < sint.Z d.minRev)
  size : ∀ c ∈ L, GMap.size c.W ≤ P.length
  ne : ∀ c ∈ L, ∃ w, (c.W !! w).isSome

theorem mvcc.CohortsPre.nil (W : GMap Loc mvcc.WatchRange) (ST : GMap Loc mvcc.WatcherSt) :
    mvcc.CohortsPre W ST [] [] :=
  ⟨by simp, List.Pairwise.nil, by simp, by simp, by simp, List.Pairwise.nil, by simp, by simp⟩

theorem mvcc.cohort_mem_of_W {W : GMap Loc mvcc.WatchRange} {ST : GMap Loc mvcc.WatcherSt}
    {P : List Loc} {L : List mvcc.Cohort} (h : mvcc.CohortsPre W ST P L) {c : mvcc.Cohort}
    (hc : c ∈ L) {x : Loc} (hx : (c.W !! x).isSome) : x ∈ P := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hx
  exact (h.sub c hc x r hr).2

/-- A member joins the last cohort. -/
theorem mvcc.CohortsPre.join {W : GMap Loc mvcc.WatchRange} {ST : GMap Loc mvcc.WatcherSt}
    {P : List Loc} {L0 : List mvcc.Cohort} {c : mvcc.Cohort} {w : Loc} {r : mvcc.WatchRange}
    {st : mvcc.WatcherSt} (h : mvcc.CohortsPre W ST P (L0 ++ [c])) (hW : W !! w = some r)
    (hst : ST !! w = some st) (hwP : w ∉ P)
    (hge : ∀ x ∈ P, ∀ sx, ST !! x = some sx → sint.Z sx.minRev ≤ sint.Z st.minRev)
    (hle : sint.Z st.minRev ≤ sint.Z c.minRev + 1000) :
    mvcc.CohortsPre W ST (P ++ [w]) (L0 ++ [{ c with W := <[w := r]> c.W }]) := by
  have hcL : c ∈ L0 ++ [c] := by simp
  have hcw : c.W !! w = none := by
    cases h1 : c.W !! w with
    | none => rfl
    | some _ => exact absurd (mvcc.cohort_mem_of_W h hcL (by rw [h1]; rfl)) hwP
  have hins : ∀ x, (<[w := r]> c.W) !! x = if w = x then some r else c.W !! x :=
    fun x => GMap.lookup_insert_eq_iff _ _ _ _
  have hdisj := h.disj
  rw [List.pairwise_append] at hdisj
  obtain ⟨hd0, -, hdc⟩ := hdisj
  have hsorted := h.sorted
  rw [List.pairwise_append] at hsorted
  obtain ⟨hs0, -, hsc⟩ := hsorted
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd x rx hx
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨a, b⟩ := h.sub d (List.mem_append_left _ hd) x rx hx; exact ⟨a, List.mem_append_left _ b⟩
    · simp at hd; subst hd
      simp only at hx
      rw [hins] at hx
      by_cases hwx : w = x
      · subst hwx; rw [if_pos rfl] at hx; obtain rfl := Option.some.inj hx; exact ⟨hW, by simp⟩
      · rw [if_neg hwx] at hx
        obtain ⟨a, b⟩ := h.sub c hcL x rx hx; exact ⟨a, List.mem_append_left _ b⟩
  · rw [List.pairwise_append]
    refine ⟨hd0, List.pairwise_singleton _ _, ?_⟩
    intro d hd d' hd' x hx
    simp at hd'; subst hd'
    simp only
    rw [hins]
    have hxw : w ≠ x := fun e => hwP (e ▸ mvcc.cohort_mem_of_W h (List.mem_append_left _ hd) hx)
    rw [if_neg hxw]
    exact hdc d hd c (by simp) x hx
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨d, hd, hdx⟩ := h.cover x hx
      rcases List.mem_append.1 hd with hd | hd
      · exact ⟨d, List.mem_append_left _ hd, hdx⟩
      · simp at hd; subst hd
        refine ⟨{ d with W := <[w := r]> d.W }, by simp, ?_⟩
        simp only; rw [hins]
        by_cases hwx : w = x
        · rw [if_pos hwx]; rfl
        · rw [if_neg hwx]; exact hdx
    · simp at hx; subst hx
      exact ⟨{ c with W := <[x := r]> c.W }, by simp, by simp only; rw [hins, if_pos rfl]; rfl⟩
  · intro d hd x sx hx hsx
    rcases List.mem_append.1 hd with hd | hd
    · exact h.window d (List.mem_append_left _ hd) x sx hx hsx
    · simp at hd; subst hd
      simp only at hx ⊢
      rw [hins] at hx
      by_cases hwx : w = x
      · subst hwx
        rw [hst] at hsx; cases hsx
        obtain ⟨a, sa, haP, -, hsa, hsaeq⟩ := h.anchor c hcL
        have := hge a haP sa hsa
        rw [hsaeq] at this
        exact ⟨this, hle⟩
      · rw [if_neg hwx] at hx
        exact h.window c hcL x sx hx hsx
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨a, sa, h1, h2, h3, h4⟩ := h.anchor d (List.mem_append_left _ hd)
      exact ⟨a, sa, List.mem_append_left _ h1, h2, h3, h4⟩
    · simp at hd; subst hd
      obtain ⟨a, sa, h1, h2, h3, h4⟩ := h.anchor c hcL
      refine ⟨a, sa, List.mem_append_left _ h1, ?_, h3, h4⟩
      simp only; rw [hins]
      by_cases hwa : w = a
      · rw [if_pos hwa]; rfl
      · rw [if_neg hwa]; exact h2
  · rw [List.pairwise_append]
    exact ⟨hs0, List.pairwise_singleton _ _, fun d hd d' hd' => by
      simp at hd'; subst hd'; exact hsc d hd c (by simp)⟩
  · intro d hd
    simp only [List.length_append, List.length_singleton]
    rcases List.mem_append.1 hd with hd | hd
    · have := h.size d (List.mem_append_left _ hd); omega
    · simp at hd; subst hd
      simp only
      rw [GMap.map_size_insert_None _ _ _ hcw]
      have := h.size c hcL; omega
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h.ne d (List.mem_append_left _ hd)
    · simp at hd; subst hd
      exact ⟨w, by simp only; rw [hins, if_pos rfl]; rfl⟩

/-- A member starts a new cohort. -/
theorem mvcc.CohortsPre.new {W : GMap Loc mvcc.WatchRange} {ST : GMap Loc mvcc.WatcherSt}
    {P : List Loc} {L : List mvcc.Cohort} {w g : Loc} {r : mvcc.WatchRange}
    {st : mvcc.WatcherSt} (h : mvcc.CohortsPre W ST P L) (hW : W !! w = some r)
    (hst : ST !! w = some st) (hwP : w ∉ P)
    (hgt : ∀ c ∈ L, sint.Z c.minRev + 1000 < sint.Z st.minRev) :
    mvcc.CohortsPre W ST (P ++ [w]) (L ++ [⟨st.minRev, g, <[w := r]> ∅⟩]) := by
  have hins : ∀ x, (<[w := r]> (∅ : GMap Loc mvcc.WatchRange)) !! x = if w = x then some r else none :=
    fun x => GMap.lookup_insert_eq_iff _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd x rx hx
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨a, b⟩ := h.sub d hd x rx hx; exact ⟨a, List.mem_append_left _ b⟩
    · simp at hd; subst hd
      simp only at hx; rw [hins] at hx
      by_cases hwx : w = x
      · subst hwx; rw [if_pos rfl] at hx; obtain rfl := Option.some.inj hx; exact ⟨hW, by simp⟩
      · rw [if_neg hwx] at hx; cases hx
  · rw [List.pairwise_append]
    refine ⟨h.disj, List.pairwise_singleton _ _, ?_⟩
    intro d hd d' hd' x hx
    simp at hd'; subst hd'
    simp only; rw [hins]
    have hxw : w ≠ x := fun e => hwP (e ▸ mvcc.cohort_mem_of_W h hd hx)
    rw [if_neg hxw]
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨d, hd, hdx⟩ := h.cover x hx
      exact ⟨d, List.mem_append_left _ hd, hdx⟩
    · simp at hx; subst hx
      exact ⟨⟨st.minRev, g, <[x := r]> ∅⟩, by simp, by simp only; rw [hins, if_pos rfl]; rfl⟩
  · intro d hd x sx hx hsx
    rcases List.mem_append.1 hd with hd | hd
    · exact h.window d hd x sx hx hsx
    · simp at hd; subst hd
      simp only at hx ⊢; rw [hins] at hx
      by_cases hwx : w = x
      · subst hwx; rw [hst] at hsx; cases hsx; omega
      · rw [if_neg hwx] at hx; cases hx
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨a, sa, h1, h2, h3, h4⟩ := h.anchor d hd
      exact ⟨a, sa, List.mem_append_left _ h1, h2, h3, h4⟩
    · simp at hd; subst hd
      exact ⟨w, st, by simp, by simp only; rw [hins, if_pos rfl]; rfl, hst, rfl⟩
  · rw [List.pairwise_append]
    exact ⟨h.sorted, List.pairwise_singleton _ _, fun d hd d' hd' => by
      simp at hd'; subst hd'; exact hgt d hd⟩
  · intro d hd
    simp only [List.length_append, List.length_singleton]
    rcases List.mem_append.1 hd with hd | hd
    · have := h.size d hd; omega
    · simp at hd; subst hd
      simp only
      rw [GMap.map_size_insert_None _ _ _ (GMap.lookup_empty w), GMap.map_size_empty]
      omega
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h.ne d hd
    · simp at hd; subst hd
      exact ⟨w, by simp only; rw [hins, if_pos rfl]; rfl⟩

theorem mvcc.cohortsByRevision.wp_proof
    (hSlice : sort.Slice.spec (GF := GF) (hG := hG))
    (hNew : mvcc.newWatcherGroup.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG)) :
    mvcc.cohortsByRevision.spec (GF := GF) (hG := hG) := by
  have hAddG := mvcc.watcherGroup.add.spec_group hAdd
  intro wg W ST cr
  wp_start as ⟨Hg, HST, %Hdom⟩
  icases mvcc.ownWatcherGroup_fixed wg W $$ Hg with ⟨Hg, #Hfix⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HmaxB, -⟩
  icases mvcc.ownWatcherGroup_watchers wg W $$ Hg with ⟨%v, Hwg, Hws, Hback⟩
  iunfold mvcc.ownWatcherSet at Hws
  obtain ⟨HdomS, HnonNeg, HszW⟩ := Hdom
  wp_auto
  wp_apply wp_map_len $$ Hws as Hws
  have hszD : GMap.size (domSet W) = GMap.size W := GMap.size_dom W
  have hle0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (GMap.size (domSet W) : Int)) := by
    rw [hszD]; constructor <;> word
  wp_apply wp_slice_make3 (V := Loc) (W64 0) (W64 (GMap.size (domSet W) : Int)) hle0
    as %sl0 ⟨Hsl0, Hcap0, -⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (sl : GoSlice) (l : List Loc) (wv : Loc),
      "sorted" ∷ sorted_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* l ∗ "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
      "w" ∷ w_ptr ↦ wv ∗ "HST" ∷ mvcc.ownStates ST ∗
      "compactionRev" ∷ compactionRev_ptr ↦ cr ∗
      "%Hi" ∷ ⌜0 ≤ i ∧ l = (keys.take i.toNat).filter (mvcc.cohortKeep ST cr)⌝)) $$ Hws
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [sorted Hsl0 Hcap0 w HST compactionRev]
  · iexists _, _, _
    simp only [named]
    iframe
    ipureintro
    exact ⟨Int.le_refl _, by simp⟩
  isplitr
  · imodintro
    iintro %i %key %u ⟨%Hkey, %Hu⟩ HP
    iNamed HP
    have hWk : (W !! key).isSome := by
      rw [GMap.domSet, GMap.lookup_fmap] at Hu
      cases h : W !! key with
      | none => rw [h] at Hu; cases Hu
      | some _ => rfl
    obtain ⟨st, hst⟩ : ∃ st, ST !! key = some st := Option.isSome_iff_exists.1 (HdomS key hWk)
    iunfold mvcc.ownStates at HST
    icases (BigSepM.bigSepM_lookup_acc hst).1 $$ HST with ⟨Hw, HST⟩
    iunfold mvcc.watcherOwn at Hw
    icases Hw with ⟨Hmin, Hvic, Hcomp, Hres, Hch⟩
    wp_auto
    have Hstep : (keys.take (i + 1).toNat).filter (mvcc.cohortKeep ST cr) =
        (keys.take i.toNat).filter (mvcc.cohortKeep ST cr) ++
          (if sint.Z cr ≤ sint.Z st.minRev then [key] else []) := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
      simp only [Option.toList_some, List.filter_append]
      by_cases h : sint.Z cr ≤ sint.Z st.minRev <;> simp [mvcc.cohortKeep, hst, h]
    wp_if_destruct
    · (try wp_auto)
      ihave HST := HST $$ [Hmin Hvic Hcomp Hres Hch]
      · iunfold mvcc.watcherOwn; iframe
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, _
      simp only [named]
      iunfold mvcc.ownStates
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [Hstep, if_neg (by omega), List.append_nil]; exact Hi.2
    · (try wp_auto)
      wp_apply wp_slice_literal (V := Loc) [key]
      isplitr
      · ipureintro; rfl
      iintro %r ⟨Hr, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hr] as %sl' ⟨Hsl, Hcap, -⟩
      (try wp_auto)
      ihave HST := HST $$ [Hmin Hvic Hcomp Hres Hch]
      · iunfold mvcc.watcherOwn; iframe
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, _
      simp only [named]
      iunfold mvcc.ownStates
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [Hstep, if_pos (by omega), Hi.2]
  iintro HP Hws
  iNamed HP
  wp_auto
  rw [show (GMap.size (domSet W) : Int).toNat = keys.length by omega, List.take_length] at Hi
  obtain ⟨-, hl⟩ := Hi
  have hlmem : ∀ w, w ∈ l → (W !! w).isSome ∧ ∃ st, ST !! w = some st ∧ sint.Z cr ≤ sint.Z st.minRev := by
    intro w hw
    rw [hl, List.mem_filter] at hw
    obtain ⟨hk, hkeep⟩ := hw
    have hW : (W !! w).isSome := by
      have := (Hkset w).1 hk
      rw [GMap.domSet, GMap.lookup_fmap] at this
      cases h : W !! w with
      | none => rw [h] at this; cases this
      | some _ => rfl
    refine ⟨hW, ?_⟩
    unfold mvcc.cohortKeep at hkeep
    cases h : ST !! w with
    | none => rw [h] at hkeep; cases hkeep
    | some st => rw [h] at hkeep; exact ⟨st, rfl, by simpa using hkeep⟩
  have hlnd : l.Nodup := by rw [hl]; exact Hknodup.filter _
  have hllen : l.length ≤ 2 ^ 62 := by
    have : l.length ≤ keys.length := by rw [hl]; exact List.length_filter_le _ _
    omega
  wp_apply (hSlice sl _ l (mvcc.cohortKey ST) iprop(sorted_ptr ↦ sl ∗ mvcc.ownStates ST))
    $$ [Hsl sorted HST] as %l2 ⟨Hsl, ⟨sorted, HST⟩, %Hperm, %Hsorted⟩
  · iframe Hsl sorted HST
    isplitr
    · ipureintro; exact hllen
    iunfold sort.lessByKey
    iintro !> %l' %i %j %a %b %Hab %Φ' !> ⟨Hs, sorted, HST⟩ HΦ'
    obtain ⟨hperm', hi0, hj0, ha, hb⟩ := Hab
    ihave %Hsl' := ownSlice_len _ _ _ $$ Hs
    have hstOf : ∀ x, x ∈ l' → ∃ st, ST !! x = some st := fun x hx =>
      let ⟨st, h, _⟩ := (hlmem x (hperm'.mem_iff.1 hx)).2; ⟨st, h⟩
    obtain ⟨sta, hsta⟩ := hstOf a (List.mem_of_getElem? ha)
    obtain ⟨stb, hstb⟩ := hstOf b (List.mem_of_getElem? hb)
    have hia : sint.Z i < sint.Z sl.len := by
      have := (List.getElem?_eq_some_iff.1 ha).1; rw [Hsl'.1] at this; word
    have hjb : sint.Z j < sint.Z sl.len := by
      have := (List.getElem?_eq_some_iff.1 hb).1; rw [Hsl'.1] at this; word
    wp_auto
    rw [ite_eq_left ⟨hi0, hia⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) l' (DFrac.own 1) a hi0 $$ [Hs] as Hs
    · iframe; ipureintro; exact ha
    iunfold mvcc.ownStates at HST
    icases (BigSepM.bigSepM_lookup_acc hsta).1 $$ HST with ⟨Hw, HST⟩
    iunfold mvcc.watcherOwn at Hw
    icases Hw with ⟨Hmin, Hrest⟩
    wp_auto
    ihave HST := HST $$ [Hmin Hrest]
    · iunfold mvcc.watcherOwn; iframe
    (try wp_auto)
    rw [ite_eq_left ⟨hj0, hjb⟩]
    wp_apply wp_load_slice_index sl (sint.Z j) l' (DFrac.own 1) b hj0 $$ [Hs] as Hs
    · iframe; ipureintro; exact hb
    icases (BigSepM.bigSepM_lookup_acc hstb).1 $$ HST with ⟨Hw, HST⟩
    iunfold mvcc.watcherOwn at Hw
    icases Hw with ⟨Hmin, Hrest⟩
    wp_auto
    ihave HST := HST $$ [Hmin Hrest]
    · iunfold mvcc.watcherOwn; iframe
    (try wp_auto)
    have hk : decide (mvcc.cohortKey ST a < mvcc.cohortKey ST b) =
        decide (sint.Z sta.minRev < sint.Z stb.minRev) := by
      simp [mvcc.cohortKey, hsta, hstb]
    rw [← hk]
    iapply HΦ'
    iunfold mvcc.ownStates
    iframe
  have hl2nd : l2.Nodup := Hperm.nodup_iff.1 hlnd
  have hl2mem : ∀ x, x ∈ l2 → (W !! x).isSome ∧ ∃ st, ST !! x = some st ∧ sint.Z cr ≤ sint.Z st.minRev :=
    fun x hx => hlmem x (Hperm.mem_iff.2 hx)
  have hl2len : l2.length ≤ 2 ^ 62 := by rw [← Hperm.length_eq]; exact hllen
  ihave %Hsl2 := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (k : w64) (cs : GoSlice) (L : List mvcc.Cohort) (wv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "w" ∷ w_ptr ↦ wv ∗ "cohorts" ∷ cohorts_ptr ↦ cs ∗
      "Hcs" ∷ cs ↦* (L.map mvcc.Cohort.val) ∗ "Hccap" ∷ ownSliceCap revCohort cs (DFrac.own 1) ∗
      "Hgs" ∷ ([∗list] c ∈ L, mvcc.ownWatcherGroup c.wg c.W) ∗
      "Hsl" ∷ sl ↦* l2 ∗ "HST" ∷ mvcc.ownStates ST ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ l2.length ∧
        mvcc.CohortsPre W ST (l2.take (sint.nat k)) L⌝) $$ [i w cohorts Hsl HST]
  · iexists W64 0, slice.nil, [], _
    simp only [named, List.map_nil]
    iframe
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro
    refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    exact mvcc.CohortsPre.nil W ST
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z sl.len := by simpa using Hif
    have hklt : sint.nat k < l2.length := by
      rw [Hsl2.1]; show (sint.Z k).toNat < (sint.Z sl.len).toNat; omega
    obtain ⟨x, hx⟩ : ∃ x, l2[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hklt⟩
    have hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := ⟨Hk.1, Hif'⟩
    rw [ite_eq_left hbnd]
    wp_apply wp_load_slice_index sl (sint.Z k) l2 (DFrac.own 1) x Hk.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hx
    (try wp_auto)
    obtain ⟨hxW, stx, hstx, hcrx⟩ := hl2mem x (List.mem_of_getElem? hx)
    obtain ⟨rx, hrx⟩ := Option.isSome_iff_exists.1 hxW
    have hxP : x ∉ l2.take (sint.nat k) := by
      intro hm
      obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hm
      rw [List.getElem_take] at hjk
      have hj' : l2[j]? = some x := by
        rw [List.getElem?_eq_getElem (by simp at hj; omega)]; exact congrArg some hjk
      have := list_nodup_getElem?_inj l2 hl2nd j (sint.nat k) x hj' hx
      simp at hj; omega
    have hge : ∀ y ∈ l2.take (sint.nat k), ∀ sy, ST !! y = some sy →
        sint.Z sy.minRev ≤ sint.Z stx.minRev := by
      intro y hy sy hsy
      obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
      rw [List.getElem_take] at hjy
      have hj' : l2[j]? = some y := by
        rw [List.getElem?_eq_getElem (by simp at hj; omega)]; exact congrArg some hjy
      have := Hsorted j (sint.nat k) y x hj' hx (by simp at hj; omega)
      simpa [mvcc.cohortKey, hsy, hstx] using this
    have hx0 : 0 ≤ sint.Z stx.minRev := HnonNeg x stx hxW hstx
    icases (BigSepM.bigSepM_lookup_acc (m := W) (by rw [gmap_get?_eq]; exact hrx)).1 $$ Hfix
      with ⟨⟨%fcs, #Hfx⟩, -⟩
    ihave %Hcsl := ownSlice_len _ _ _ $$ Hcs
    have hP := Hk.2.2
    have hk1 : sint.Z (k + W64 1) = sint.Z k + 1 := by
      have := Hif'; word
    have hklt' : sint.Z k < l2.length := by
      have : (sint.Z k).toNat < l2.length := hklt
      omega
    have hksucc : l2.take (sint.nat (k + W64 1)) = l2.take (sint.nat k) ++ [x] := by
      have : sint.nat (k + W64 1) = sint.nat k + 1 := by
        show (sint.Z (k + W64 1)).toNat = (sint.Z k).toNat + 1
        omega
      rw [this, List.take_add_one, hx]; simp
    by_cases hL : L = []
    · subst hL
      have hcs0 : sint.Z cs.len = 0 := by
        have h1 : (0 : Nat) = (sint.Z cs.len).toNat := by simpa using Hcsl.1
        have h2 := Hcsl.2; omega
      wp_if_destruct
      · exfalso; simp at Hif; omega
      (try wp_auto)
      wp_apply hNew as %v' Hnew
      (try wp_auto)
      ihave Hg0 := Hnew $$ %g_ptr g
      wp_apply (hAddG g_ptr ∅ x rx fcs) $$ [$Hg0 $Hfx] as Hg0
      · ipureintro; exact ⟨GMap.lookup_empty x, by rw [GMap.map_size_empty]; decide⟩
      iunfold mvcc.ownStates at HST
      icases (BigSepM.bigSepM_lookup_acc hstx).1 $$ HST with ⟨Hwx, HST⟩
      iunfold mvcc.watcherOwn at Hwx
      icases Hwx with ⟨Hmin, Hrest⟩
      (try wp_auto)
      wp_apply wp_slice_literal (V := revCohort) [({ minRev' := stx.minRev, wg' := g_ptr } : revCohort)]
      isplitr
      · ipureintro; rfl
      iintro %r1 ⟨Hr1, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hcs $Hccap $Hr1] as %cs' ⟨Hcs, Hccap, -⟩
      (try wp_auto)
      ihave HST := HST $$ [Hmin Hrest]
      · iunfold mvcc.watcherOwn; iframe
      wp_for_post
      iframe
      iexists k + W64 1, cs', [⟨stx.minRev, g_ptr, <[x := rx]> ∅⟩], x
      simp only [named, List.map_cons, List.map_nil]
      iunfold mvcc.ownStates
      iframe
      ipureintro
      refine ⟨by omega, by omega, ?_⟩
      rw [hksucc]
      simpa using mvcc.CohortsPre.new (g := g_ptr) hP hrx hstx hxP (by simp)
    · obtain ⟨L0, c, rfl⟩ : ∃ L0 c, L = L0 ++ [c] :=
        ⟨L.dropLast, L.getLast hL, (List.dropLast_concat_getLast hL).symm⟩
      have hlenL : sint.Z cs.len = (L0.length : Int) + 1 := by
        have h1 : L0.length + 1 = (sint.Z cs.len).toNat := by simpa using Hcsl.1
        have h2 := Hcsl.2; omega
      wp_if_destruct
      rotate_left
      · exfalso; simp at Hif; omega
      iunfold mvcc.ownStates at HST
      icases (BigSepM.bigSepM_lookup_acc hstx).1 $$ HST with ⟨Hwx, HST⟩
      iunfold mvcc.watcherOwn at Hwx
      icases Hwx with ⟨Hmin, Hrest⟩
      have hidx : sint.Z (cs.len - W64 1) = (L0.length : Int) := by
        have := Hcsl.2; word
      have hcv : ((L0 ++ [c]).map mvcc.Cohort.val)[(sint.Z (cs.len - W64 1)).toNat]? = some c.val := by
        rw [hidx]; simp
      icases ownSlice_elem_acc (sint.Z (cs.len - W64 1)) c.val cs (DFrac.own 1) _
        (by rw [hidx]; omega) hcv $$ Hcs with ⟨Hel, Hcsb⟩
      have hib : 0 ≤ sint.Z (cs.len - W64 1) ∧ sint.Z (cs.len - W64 1) < sint.Z cs.len := by
        rw [hidx]; omega
      (try wp_auto)
      rw [ite_eq_left hib]
      (try wp_auto)
      have hcL : c ∈ L0 ++ [c] := by simp
      obtain ⟨a, sa, haP, haW, hsa, hsaeq⟩ := hP.anchor c hcL
      have hc0 : 0 ≤ sint.Z c.minRev := by
        rw [← hsaeq]
        obtain ⟨ra, hra⟩ := Option.isSome_iff_exists.1 haW
        exact HnonNeg a sa (by rw [(hP.sub c hcL a ra hra).1]; rfl) hsa
      have hcx : sint.Z c.minRev ≤ sint.Z stx.minRev := by
        rw [← hsaeq]; exact hge a haP sa hsa
      have hsub : sint.Z (stx.minRev - c.minRev) = sint.Z stx.minRev - sint.Z c.minRev := by
        word
      rw [hsub, show sint.Z (W64 1000) = 1000 from rfl]
      wp_if_destruct
      · -- join the last cohort
        (try wp_auto)
        rw [ite_eq_left hib]
        (try wp_auto)
        icases (BigSepL.bigSepL_append).1 $$ Hgs with ⟨Hgs0, Hgc⟩
        icases BigSepL.bigSepL_singleton.1 $$ Hgc with Hgc
        have hcw : c.W !! x = none := by
          cases h1 : c.W !! x with
          | none => rfl
          | some _ => exact absurd (mvcc.cohort_mem_of_W hP hcL (by rw [h1]; rfl)) hxP
        have hcsz : GMap.size c.W + 1 < 2 ^ 63 := by
          have := hP.size c hcL
          have : (l2.take (sint.nat k)).length ≤ l2.length := by rw [List.length_take]; omega
          omega
        wp_apply (hAddG c.wg c.W x rx fcs) $$ [$Hgc $Hfx] as Hgc
        · ipureintro; exact ⟨hcw, hcsz⟩
        ihave Hcs := Hcsb $$ Hel
        rw [list_set_lookup_self _ _ _ hcv]
        ihave HST := HST $$ [Hmin Hrest]
        · iunfold mvcc.watcherOwn; iframe
        ihave Hgs : [∗list] c ∈ L0 ++ [{ c with W := <[x := rx]> c.W }], mvcc.ownWatcherGroup c.wg c.W
          $$ [Hgs0 Hgc]
        · iapply (BigSepL.bigSepL_append).2
          iframe Hgs0
          iapply BigSepL.bigSepL_singleton.2
          iexact Hgc
        wp_for_post
        iframe
        iexists k + W64 1, cs, L0 ++ [{ c with W := <[x := rx]> c.W }], x
        simp only [named]
        have hval : (L0 ++ [{ c with W := <[x := rx]> c.W }]).map mvcc.Cohort.val =
            (L0 ++ [c]).map mvcc.Cohort.val := by simp [mvcc.Cohort.val]
        rw [hval]
        iunfold mvcc.ownStates
        iframe
        ipureintro
        refine ⟨by omega, by omega, ?_⟩
        rw [hksucc]
        exact mvcc.CohortsPre.join hP hrx hstx hxP hge (by omega)
      · -- a new cohort
        (try wp_auto)
        ihave Hcs := Hcsb $$ Hel
        rw [list_set_lookup_self _ _ _ hcv]
        have hgt : ∀ d ∈ L0 ++ [c], sint.Z d.minRev + 1000 < sint.Z stx.minRev := by
          intro d hd
          simp only [List.mem_append, List.mem_singleton] at hd
          rcases hd with hd | rfl
          · have hs := hP.sorted
            rw [List.pairwise_append] at hs
            have := hs.2.2 d hd c (by simp)
            omega
          · omega
        wp_apply hNew as %v' Hnew
        (try wp_auto)
        ihave Hg0 := Hnew $$ %g_ptr g
        wp_apply (hAddG g_ptr ∅ x rx fcs) $$ [$Hg0 $Hfx] as Hg0
        · ipureintro; exact ⟨GMap.lookup_empty x, by rw [GMap.map_size_empty]; decide⟩
        (try wp_auto)
        wp_apply wp_slice_literal (V := revCohort) [({ minRev' := stx.minRev, wg' := g_ptr } : revCohort)]
        isplitr
        · ipureintro; rfl
        iintro %r1 ⟨Hr1, -⟩
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hcs $Hccap $Hr1] as %cs' ⟨Hcs, Hccap, -⟩
        (try wp_auto)
        ihave HST := HST $$ [Hmin Hrest]
        · iunfold mvcc.watcherOwn; iframe
        ihave Hgs : [∗list] c ∈ (L0 ++ [c]) ++ [(⟨stx.minRev, g_ptr, <[x := rx]> ∅⟩ : mvcc.Cohort)],
            mvcc.ownWatcherGroup c.wg c.W $$ [Hgs Hg0]
        · iapply (BigSepL.bigSepL_append).2
          iframe Hgs
          iapply BigSepL.bigSepL_singleton.2
          iexact Hg0
        wp_for_post
        iframe
        iexists k + W64 1, cs', (L0 ++ [c]) ++ [⟨stx.minRev, g_ptr, <[x := rx]> ∅⟩], x
        simp only [named, List.map_append, List.map_cons, List.map_nil]
        iunfold mvcc.ownStates
        iframe
        ipureintro
        refine ⟨by omega, by omega, ?_⟩
        rw [hksucc]
        exact mvcc.CohortsPre.new (g := g_ptr) hP hrx hstx hxP hgt
  · -- done: every member grouped
    (try wp_auto)
    have hkl : sint.nat k = l2.length := by
      rw [Hsl2.1]; show (sint.Z k).toNat = (sint.Z sl.len).toNat
      have := Hk.2.1; have := Hsl2.1
      have : (sint.Z sl.len).toNat = l2.length := by rw [Hsl2.1]
      omega
    have hP := Hk.2.2
    rw [hkl, List.take_length] at hP
    iapply HΦ
    iexists L
    iframe
    isplitl [Hback Hwg Hws]
    · iapply Hback $$ Hwg
      iunfold mvcc.ownWatcherSet; iexact Hws
    ipureintro
    refine ⟨fun c hc w r h => (hP.sub c hc w r h).1, hP.disj, ?_, ?_, hP.window, ?_, hP.sorted⟩
    · intro w r st hW hst hcr
      have hk : w ∈ keys := (Hkset w).2 (by rw [GMap.domSet, GMap.lookup_fmap, hW]; rfl)
      have hl' : w ∈ l := by
        rw [hl, List.mem_filter]
        exact ⟨hk, by simp [mvcc.cohortKeep, hst, hcr]⟩
      exact hP.cover w (Hperm.mem_iff.1 hl')
    · intro c hc w st hw hst
      obtain ⟨-, st', hst', hcr⟩ := hl2mem w (mvcc.cohort_mem_of_W hP hc hw)
      rw [hst] at hst'; cases hst'; exact hcr
    · intro c hc
      obtain ⟨a, sa, -, h2, h3, h4⟩ := hP.anchor c hc
      exact ⟨a, sa, h2, h3, h4⟩
