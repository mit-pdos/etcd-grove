/-
Lean-first (no Rocq counterpart).

# lintest: what `Run` concludes from the clients' results (2026-10-14)

After `wg.Wait()`, `Run` holds every client's trace `hs[c]` and ghost value `ps[c]`
(`ClientsOk`: client `c`'s records match its trace, `ops` of them). With the invariant's view
(`InvOk`, the ghost map agreeing with every `ps[c]`), the traces' concatenation, which `Run`
passes to porcupine, is linearizable (`final_linearizable`, through `LogOk.linearizable` of
`LinTheory.lean`) and satisfies porcupine's premise (`final_histOk`).

Also the heap lemmas `Run` uses: a slice as its elements' points-tos (`ownSlice_elems`), the
clients' initial ghost values (`initMap`, `initMap_alloc`), and the ghost map's agreement
with all of them (`toks_lookup`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.InvLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section pure
variable [GooseExts] {σ : Type}

/-- The clients' traces `hs` and ghost values `ps` (client `c`'s at index `c`): client `c`'s
records match its trace (`ClientOk`), and there are `mf c` of them (`RunLin2`: `ops` for the
first group, `ops2` for the second). -/
def ClientsOk (mf : Nat → Nat) (hs : List (List Operation)) (ps : List (Nat × ClientV)) : Prop :=
  hs.length = ps.length ∧ ∀ (c : Nat) (h : List Operation) (p : Nat × ClientV),
    hs[c]? = some h → ps[c]? = some p →
      p.1 = c ∧ (∃ cid, ClientOk cid h p.2.1) ∧ p.2.1.length = mf c

theorem ClientsOk.nil (mf : Nat → Nat) : ClientsOk mf [] [] :=
  ⟨rfl, fun c h p hh _ => by simp at hh⟩

theorem ClientsOk.snoc {mf : Nat → Nat} {hs : List (List Operation)} {ps : List (Nat × ClientV)}
    (H : ClientsOk mf hs ps) (cid : w64) (h : List Operation) (Lc : List (OpV × w64)) (lr : w64)
    (hok : ClientOk cid h Lc) (hl : Lc.length = mf hs.length) :
    ClientsOk mf (hs ++ [h]) (ps ++ [(hs.length, (Lc, lr))]) := by
  obtain ⟨hlen, hc⟩ := H
  refine ⟨by simp [hlen], ?_⟩
  intro c h' p hh hp
  rcases Nat.lt_or_ge c hs.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hh
    rw [List.getElem?_append_left (by omega)] at hp
    exact hc c h' p hh hp
  · rw [List.getElem?_append_right hge] at hh
    rw [List.getElem?_append_right (by omega)] at hp
    rcases Nat.lt_or_ge (c - hs.length) 1 with h1 | h1
    · rw [show c - hs.length = 0 by omega] at hh
      rw [show c - ps.length = 0 by omega] at hp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hh hp
      subst hh hp
      have hc' : c = hs.length := by omega
      exact ⟨by simp; omega, ⟨cid, hok⟩, by rw [hc']; exact hl⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at hh
      cases hh

/-- Client `c`'s trace has `mf c` operations. -/
theorem ClientsOk.length {mf : Nat → Nat} {hs : List (List Operation)} {ps : List (Nat × ClientV)}
    (hc : ClientsOk mf hs ps) {c : Nat} {h : List Operation} (hh : hs[c]? = some h) :
    h.length = mf c := by
  have hcl : c < ps.length := by
    rw [← hc.1]; exact (List.getElem?_eq_some_iff.1 hh).1
  obtain ⟨p, hp⟩ : ∃ p, ps[c]? = some p := ⟨_, List.getElem?_eq_getElem hcl⟩
  obtain ⟨-, ⟨cid, hok⟩, hl⟩ := hc.2 c h p hh hp
  rw [hok.1, hl]

/-- The records of the clients, as `LinTheory`'s `Lcs`. -/
def recsList (ps : List (Nat × ClientV)) : List (List (OpV × Int)) :=
  ps.map fun p => p.2.1.map fun q => (q.1, sint.Z q.2)

theorem histOf_flatten (hs : List (List Operation)) :
    histOf hs.flatten = (hs.map histOf).flatten := by
  unfold histOf
  rw [List.map_flatten]

theorem final_logOk {M : SeqModel σ OpV} {n : Nat} {mf : Nat → Nat} {s : σ} {t : w64}
    {L : List (LinRec OpV)}
    {Ls : GMap Nat ClientV} {hs : List (List Operation)} {ps : List (Nat × ClientV)}
    (H : InvOk M n s t L Ls) (hc : ClientsOk mf hs ps) (hn : hs.length = n)
    (hlook : ∀ p ∈ ps, Ls.lookup p.1 = some p.2) :
    LogOk M (hs.map histOf) (recsList ps) L where
  len := by simp [recsList, hc.1]
  lclen := by
    intro c h' Lc' hh' hLc'
    rw [List.getElem?_map] at hh'
    unfold recsList at hLc'
    rw [List.getElem?_map] at hLc'
    cases hh : hs[c]? with
    | none => rw [hh] at hh'; cases hh'
    | some h =>
      cases hp : ps[c]? with
      | none => rw [hp] at hLc'; cases hLc'
      | some p =>
        rw [hh] at hh'
        rw [hp] at hLc'
        simp only [Option.map_some, Option.some.injEq] at hh' hLc'
        subst hh' hLc'
        obtain ⟨-, ⟨cid, hok⟩, -⟩ := hc.2 c h p hh hp
        simp only [histOf, List.length_map]
        exact hok.1.symm
  recs := by
    intro c h' Lc' hh' hLc' j o q' ho hq'
    rw [List.getElem?_map] at hh'
    unfold recsList at hLc'
    rw [List.getElem?_map] at hLc'
    cases hh : hs[c]? with
    | none => rw [hh] at hh'; cases hh'
    | some h =>
      cases hp : ps[c]? with
      | none => rw [hp] at hLc'; cases hLc'
      | some p =>
        rw [hh] at hh'
        rw [hp] at hLc'
        simp only [Option.map_some, Option.some.injEq] at hh' hLc'
        subst hh' hLc'
        obtain ⟨-, ⟨cid, hok⟩, -⟩ := hc.2 c h p hh hp
        simp only [histOf, List.getElem?_map] at ho
        rw [List.getElem?_map] at hq'
        cases hoj : h[j]? with
        | none => rw [hoj] at ho; cases ho
        | some op =>
          cases hqj : p.2.1[j]? with
          | none => rw [hqj] at hq'; cases hq'
          | some q =>
            rw [hoj] at ho
            rw [hqj] at hq'
            simp only [Option.map_some, Option.some.injEq] at ho hq'
            subst ho hq'
            obtain ⟨-, hio, hcall, hret⟩ := hok.2 j op q hoj hqj
            exact ⟨hio, hcall, hret⟩
  filt := by
    intro c
    rw [H.filt c]
    rcases Nat.lt_or_ge c ps.length with hlt | hge
    · obtain ⟨p, hp⟩ : ∃ p, ps[c]? = some p := ⟨_, List.getElem?_eq_getElem hlt⟩
      have hcl : c < hs.length := by rw [hc.1]; exact hlt
      obtain ⟨h, hh⟩ : ∃ h, hs[c]? = some h := ⟨_, List.getElem?_eq_getElem hcl⟩
      obtain ⟨hpc, -, -⟩ := hc.2 c h p hh hp
      have hl := hlook p (List.mem_of_getElem? hp)
      rw [hpc] at hl
      simp only [recsOf, hl, Option.map_some, Option.getD_some, toRecs, recsList,
        List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    · have hnone : Ls.lookup c = none := by
        cases hl : Ls.lookup c with
        | none => rfl
        | some v =>
          have := H.dom c v hl
          rw [← hn, hc.1] at this
          omega
      have hg : (recsList ps).getD c [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [recsList]; omega)]
        rfl
      simp only [recsOf, hnone, Option.map_none, Option.getD_none, hg, toRecs, List.map_nil]
  sorted := H.sorted
  runs := by rw [H.runs]; rfl

/-- **The traced history is linearizable.** -/
theorem final_linearizable {M : SeqModel σ OpV} {n : Nat} {mf : Nat → Nat} {s : σ} {t : w64}
    {L : List (LinRec OpV)} {Ls : GMap Nat ClientV} {hs : List (List Operation)}
    {ps : List (Nat × ClientV)}
    (H : InvOk M n s t L Ls) (hc : ClientsOk mf hs ps) (hn : hs.length = n)
    (hlook : ∀ p ∈ ps, Ls.lookup p.1 = some p.2) :
    Linearizable M (histOf hs.flatten) := by
  rw [histOf_flatten]
  exact (final_logOk H hc hn hlook).linearizable

/-- **The traced history satisfies porcupine's premise.** -/
theorem final_histOk {mf : Nat → Nat} {hs : List (List Operation)} {ps : List (Nat × ClientV)}
    (hc : ClientsOk mf hs ps) (hb : (hs.flatten.length : Int) < 2 ^ 60) :
    HistOk hs.flatten := by
  refine ⟨hb, ?_⟩
  intro o ho
  obtain ⟨h, hh, hoh⟩ := List.mem_flatten.1 ho
  obtain ⟨c, hc'⟩ := List.getElem?_of_mem hh
  have hcl : c < ps.length := by
    rw [← hc.1]; exact (List.getElem?_eq_some_iff.1 hc').1
  obtain ⟨p, hp⟩ : ∃ p, ps[c]? = some p := ⟨_, List.getElem?_eq_getElem hcl⟩
  obtain ⟨-, ⟨cid, hok⟩, -⟩ := hc.2 c h p hc' hp
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hoh
  have hjl : j < p.2.1.length := by
    rw [← hok.1]; exact (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨q, hq⟩ : ∃ q, p.2.1[j]? = some q := ⟨_, List.getElem?_eq_getElem hjl⟩
  obtain ⟨-, -, h1, h2⟩ := hok.2 j o q hj hq
  exact Int.le_trans h1 h2

/-- The clients' initial ghost values: `v0` for clients `0, ..., n - 1`. -/
def initMap (n : Nat) (v0 : ClientV) : GMap Nat ClientV :=
  match n with
  | 0 => ∅
  | k + 1 => (initMap k v0).insert k v0

theorem initMap_lookup (n c : Nat) (v0 : ClientV) :
    (initMap n v0).lookup c = if c < n then some v0 else none := by
  induction n with
  | zero => simp [initMap]
  | succ n ih =>
    simp only [initMap]
    rw [GMap.lookup_insert_eq_iff, ih]
    by_cases h : n = c
    · subst h; simp
    · simp only [h, ↓reduceIte]
      by_cases hc : c < n
      · simp [hc, show c < n + 1 by omega]
      · simp [hc, show ¬ c < n + 1 by omega]

theorem InvOk.init (M : SeqModel σ OpV) (n : Nat) (t0 : w64) :
    InvOk M n M.init t0 [] (initMap n ([], t0)) where
  runs := rfl
  sorted := List.Pairwise.nil
  le_t e he := by cases he
  lr_le c v hv := by
    rw [initMap_lookup] at hv
    split at hv
    · cases hv; exact Int.le_refl _
    · cases hv
  dom c v hv := by
    rw [initMap_lookup] at hv
    split at hv
    · assumption
    · cases hv
  filt c := by
    simp only [List.filter_nil, recsOf, initMap_lookup]
    split <;> rfl

/-- The traces' concatenation has `mf 0 + ... + mf (n - 1)` operations. -/
theorem final_length {n : Nat} {mf : Nat → Nat} {hs : List (List Operation)}
    {ps : List (Nat × ClientV)}
    (hc : ClientsOk mf hs ps) (hn : hs.length = n) :
    hs.flatten.length = ((List.range n).map mf).sum := by
  rw [List.length_flatten]
  congr 1
  apply List.ext_getElem (by simp [hn])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact hc.length (List.getElem?_eq_getElem (by simpa using h1))

/-- `RunLin2`'s count: the first group's `n1` clients run `m1` operations each, the second
group's `n2` run `m2`. -/
def groupOps (n1 m1 m2 : Nat) (c : Nat) : Nat := if c < n1 then m1 else m2

theorem sum_groupOps (n1 n2 m1 m2 : Nat) :
    ((List.range (n1 + n2)).map (groupOps n1 m1 m2)).sum = n1 * m1 + n2 * m2 := by
  induction n2 with
  | zero =>
    simp only [Nat.add_zero, Nat.zero_mul]
    induction n1 with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      have : ((List.range k).map (groupOps (k + 1) m1 m2)).sum = k * m1 := by
        rw [← ih]
        congr 1
        apply List.map_congr_left
        intro c hc
        have := List.mem_range.1 hc
        simp [groupOps, show c < k + 1 by omega, show c < k by omega]
      simp [this, groupOps, Nat.succ_mul]
  | succ k ih =>
    rw [show n1 + (k + 1) = (n1 + k) + 1 by omega, List.range_succ, List.map_append,
      List.sum_append, ih]
    have hg : groupOps n1 m1 m2 (n1 + k) = m2 := by
      unfold groupOps; rw [ite_eq_right (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hg, Nat.succ_mul]
    omega

/-- A `filterMap` whose function is defined on all of the list, by index. -/
theorem getElem?_filterMap_all {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).isSome) → ∀ i : Nat, (l.filterMap f)[i]? = l[i]?.bind f
  | [], _, i => by simp
  | a :: l, hall, i => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hall a List.mem_cons_self)
    rw [List.filterMap_cons, hb]
    cases i with
    | zero => simp [hb]
    | succ i =>
      simp only [List.getElem?_cons_succ]
      exact getElem?_filterMap_all f l (fun x hx => hall x (List.mem_cons_of_mem _ hx)) i

theorem length_filterMap_all {α β : Type} (f : α → Option β) (l : List α)
    (hall : ∀ a ∈ l, (f a).isSome) : (l.filterMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hall a List.mem_cons_self)
    rw [List.filterMap_cons, hb, List.length_cons, List.length_cons,
      ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))]

/-- **The operations in a linearization's order linearize themselves in their own order**,
and are all of them. -/
theorem isLinearization_reorder {α : Type} {M : SeqModel σ α} {h : List (Op α)} {π : List Nat}
    (hl : IsLinearization M h π) :
    (π.filterMap (h[·]?)).length = h.length ∧
      IsLinearization M (π.filterMap (h[·]?)) (List.range (π.filterMap (h[·]?)).length) := by
  obtain ⟨hnd, hmem, hrun, hpw⟩ := hl
  have hvalid : ∀ k ∈ π, k < h.length := fun k hk => ((hmem k).1 hk).1
  have hsome : ∀ k ∈ π, (h[k]?).isSome := fun k hk => by
    simp [List.getElem?_eq_getElem (hvalid k hk)]
  have hplen : π.length = h.length := by
    have hperm : π.Perm (List.range h.length) :=
      (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun k => by
        rw [hmem k, List.mem_range]; simp
    rw [hperm.length_eq, List.length_range]
  have hlen := length_filterMap_all (h[·]?) π hsome
  have hget := getElem?_filterMap_all (h[·]?) π hsome
  refine ⟨by rw [hlen, hplen], List.nodup_range, fun k => by simp [List.mem_range], ?_, ?_⟩
  · have hv : vals (π.filterMap (h[·]?)) (List.range (π.filterMap (h[·]?)).length) = vals h π := by
      unfold vals
      apply List.ext_getElem?
      intro i
      rw [getElem?_filterMap_all _ _ (fun k hk => by
          rw [List.mem_range] at hk
          simp [List.getElem?_eq_getElem hk]),
        getElem?_filterMap_all _ _ (fun k hk => by simp [List.getElem?_eq_getElem (hvalid k hk)])]
      by_cases hi : i < π.length
      · rw [List.getElem?_range (by rw [hlen]; exact hi)]
        simp only [Option.bind_some, hget i, List.getElem?_eq_getElem hi]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
        rfl
    rw [hv]; exact hrun
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_range]
    rintro ⟨oa, ob, ha, hb, hlt⟩
    rw [List.length_range, hlen] at hi hj
    rw [hget j, List.getElem?_eq_getElem hj, Option.bind_some] at ha
    rw [hget i, List.getElem?_eq_getElem hi, Option.bind_some] at hb
    exact (List.pairwise_iff_getElem.1 hpw) i j hi hj hij ⟨oa, ob, ha, hb, hlt⟩

/-- `isLinearization_reorder` for a slice of `Operation`s and the ids porcupine returns. -/
theorem isLinearization_order {M : SeqModel σ OpV} {os : List Operation} {xs : List w64}
    (hx : ∀ x ∈ xs, 0 ≤ sint.Z x)
    (hl : IsLinearization M (histOf os) (xs.map fun x => (sint.Z x).toNat)) :
    (∀ x ∈ xs, 0 ≤ sint.Z x ∧ (sint.Z x).toNat < os.length) ∧
      (xs.filterMap (fun x => os[(sint.Z x).toNat]?)).length = os.length ∧
      IsLinearization M (histOf (xs.filterMap (fun x => os[(sint.Z x).toNat]?)))
        (List.range (xs.filterMap (fun x => os[(sint.Z x).toNat]?)).length) := by
  have hh : histOf (xs.filterMap (fun x => os[(sint.Z x).toNat]?)) =
      (xs.map fun x => (sint.Z x).toNat).filterMap ((histOf os)[·]?) := by
    unfold histOf
    rw [List.filterMap_map, List.map_filterMap]
    congr 1
    funext x
    simp [List.getElem?_map]
  obtain ⟨h1, h2⟩ := isLinearization_reorder hl
  have hval : ∀ x ∈ xs, 0 ≤ sint.Z x ∧ (sint.Z x).toNat < os.length := by
    intro x hxm
    refine ⟨hx x hxm, ?_⟩
    have := ((hl.2.1 ((sint.Z x).toNat)).1 (List.mem_map_of_mem hxm)).1
    simpa [histOf] using this
  refine ⟨hval, ?_, ?_⟩
  · have : (xs.filterMap (fun x => os[(sint.Z x).toNat]?)).length =
        ((xs.map fun x => (sint.Z x).toNat).filterMap ((histOf os)[·]?)).length := by
      rw [← hh]; simp [histOf]
    rw [this, h1]; simp [histOf]
  · have hl2 : (xs.filterMap (fun x => os[(sint.Z x).toNat]?)).length =
        ((xs.map fun x => (sint.Z x).toNat).filterMap ((histOf os)[·]?)).length := by
      rw [← hh]; simp [histOf]
    rw [hh, hl2]; exact h2

end pure

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem bigSepL_replicate_range {A : Type} (n : Nat) (v : A) (Φ : Nat → A → IProp GF) :
    ([∗list] k ↦ x ∈ List.replicate n v, Φ k x) ⊢ [∗list] k ∈ List.range n, Φ k v := by
  induction n with
  | zero =>
    simp only [List.replicate_zero, List.range_zero]
    iintro _
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | succ n ih =>
    rw [List.replicate_succ', List.range_succ]
    iintro H
    icases BigSepL.bigSepL_snoc.1 $$ H with ⟨H1, H2⟩
    iapply BigSepL.bigSepL_snoc.2
    isplitl [H1]
    · iapply ih $$ H1
    · rw [List.length_replicate]; iexact H2

/-- A slice of `n` copies of `v` as its elements' points-tos. -/
theorem ownSlice_replicate_elems {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (n : Nat) (v : V) (dq : DFrac) :
    (s ↦*{dq} List.replicate n v : IProp GF) ⊢
      [∗list] c ∈ List.range n, typedPointsto (sliceIndexRef V ((c : Nat) : Int) s) v dq := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Hsl, %Hl⟩)
  · have hn : n = 0 := by
      have := H.2; rw [List.replicate_eq_nil_iff] at this; exact this
    subst hn
    simp only [List.range_zero]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  · icases typedPointsto_split _ _ _ $$ Hsl with Hsl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hsl with ⟨%Hlen, Hsl⟩
    unfold arrayElems
    unfold sliceIndexRef
    iapply bigSepL_replicate_range n v
      (fun (k : Nat) (x : V) => typedPointsto (GF := GF) (arrayIndexRef V (k : Int) s.ptr) x dq)
    iexact Hsl

theorem initMap_alloc_from (γ : GName) (n : Nat) (v0 : ClientV) :
    ghostMapAuth (GF := GF) γ 1 (∅ : GMap Nat ClientV) ⊢
      |==> (ghostMapAuth γ 1 (initMap n v0) ∗ [∗list] c ∈ List.range n, clientTok γ c v0) := by
  induction n with
  | zero =>
    iintro H
    imodintro
    simp only [initMap, List.range_zero]
    iframe
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | succ n ih =>
    iintro H
    imod ih $$ H with ⟨H, Hs⟩
    have hnone : (initMap n v0).lookup n = none := by
      rw [initMap_lookup]; simp
    imod ghost_map_insert n v0 hnone $$ H with ⟨H, Hn⟩
    imodintro
    simp only [initMap, List.range_succ]
    iframe H
    iapply BigSepL.bigSepL_snoc.2
    iframe

theorem initMap_alloc (n : Nat) (v0 : ClientV) :
    ⊢ |==> ∃ γ, (ghostMapAuth (GF := GF) γ 1 (initMap n v0) ∗
      [∗list] c ∈ List.range n, clientTok γ c v0) := by
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ClientV) with ⟨%γ, H⟩
  imod initMap_alloc_from γ n v0 $$ H with ⟨H, Hs⟩
  imodintro
  iexists γ
  iframe

/-- What client `c` hands back to `Run` (through the wait group): its trace `hc` in its cell of
`histories` (`hsl`), its ghost value, its records matching its trace, `m` of them, and what
porcupine's `Step` needs of the trace. -/
def clientDone {σ : Type} (S : ModelSpec GF σ) (γ : GName) (hsl : GoSlice) (m : Nat) (c : Nat) :
    IProp GF :=
  iprop(∃ (sl : GoSlice) (hc : List Operation) (Lc : List (OpV × w64)) (lr cid : w64),
    typedPointsto (sliceIndexRef GoSlice ((c : Nat) : Int) hsl) sl (DFrac.own 1) ∗ sl ↦* hc ∗
    clientTok γ c (Lc, lr) ∗ ⌜ClientOk cid hc Lc ∧ Lc.length = m⌝ ∗ opsIoOk S hc)

/-- The ghost map agrees with the clients' ghost values. -/
theorem toks_lookup (γ : GName) (q : Qp) (Ls : GMap Nat ClientV) :
    ∀ ps : List (Nat × ClientV), ghostMapAuth (GF := GF) γ q Ls ⊢
      ([∗list] p ∈ ps, clientTok γ p.1 p.2) -∗ ⌜∀ p ∈ ps, Ls.lookup p.1 = some p.2⌝
  | [] => by
    iintro _ _
    ipureintro
    intro p hp
    cases hp
  | p :: ps => by
    iintro Ha Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hp, Hs⟩
    icombine Ha Hp gives %H1
    ihave %H2 := toks_lookup γ q Ls ps $$ Ha Hs
    ipureintro
    intro p' hp'
    rcases List.mem_cons.1 hp' with h | h
    · subst h; exact H1
    · exact H2 p' h

/-- What porcupine's `Step` needs, for operations among those of a history. -/
theorem opsIoOk_sub {σ : Type} (S : ModelSpec GF σ) (os lops : List Operation)
    (h : ∀ o ∈ lops, o ∈ os) : opsIoOk S os ⊢ opsIoOk S lops := by
  unfold opsIoOk
  iintro #H
  iapply (BigSepL.bigSepL_intro (P := iprop(□ [∗list] o ∈ os, S.ioOk o.Input' o.Output'))
    (fun k x hx => by
      iintro #H'
      iapply BigSepL.bigSepL_mem (h x (List.mem_of_getElem? hx)) $$ H'))
  iexact H

/-- The empty history is linearized by the empty order. -/
theorem isLinearization_nil {σ : Type} (M : SeqModel σ OpV) :
    IsLinearization M ([] : List (Op OpV)) (List.range 0) :=
  ⟨List.nodup_nil, fun k => by simp, by simp [vals, run], List.Pairwise.nil⟩

end heap

end lintest
end EtcdGrove
end Perennial
