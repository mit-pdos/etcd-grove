/- Lean-first (no Rocq counterpart).

`HistoryRevs`' proof (notes/k8s-dist-k9.md §2.7, step 4).

- `OpReq x y u`: `u` is a revision `OpAnchors` asks of the operation `(x, y)`; `opAnchors_of`: an
  anchor list holding every such `u` satisfies `OpAnchors`.
- The ops loop keeps `∀ p ∈ xs.take j, ∀ u, OpReq p.1 p.2 u → u = 0 ∨ (A !! u).isSome` for the
  map `all` (`A`), whose keys are nonzero; `num(v)` and `obj(k, v)` both add `v` to it (`obj` also
  to `byKey`, whose contents the spec does not constrain).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HistoryRevs
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvOfMsg
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeWEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeItemRVs
public import Perennial.Spec.slices.Sort
public import Perennial.Proof.slices.Results

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj Revs)

section pure
variable [GooseExts]

/-- `OpAnchors` asks the minimum resource version of a watch and of an operation not answered
`tooLargeL` (G15, `notes/k8s-dist-k9.md`). -/
def MinOk (x : Input) (y : Output) : Prop := x.Kind' = W64 5 ∨ y.Err' ≠ W64 6

/-- `u` is a revision `OpAnchors` asks of `(x, y)` (see the file header). -/
def OpReq (x : Input) (y : Output) (u : w64) : Prop :=
  (MinOk x y ∧ parseRVD x.MinRV' = some u) ∨ (x.HasPreRV' = true ∧ parseRVD x.PreRV' = some u) ∨
  (x.Kind' = W64 5 ∧ y.WFailed' = false ∧ ∃ evs, decWEventsL y.WEvents' = some evs ∧
    ∃ e ∈ evs, e.t < 4 ∧ e.o.ResourceVersion' = u) ∨
  (x.Kind' ≠ W64 5 ∧ (u = y.ErrRV' ∨ u = y.ListRV' ∨ (y.Err' = W64 0 ∧ u = y.RV') ∨
    (x.Kind' = W64 4 ∧ y.Err' = W64 0 ∧ ∃ os : List Obj, y.Items' = encItemsL os ∧
      ∃ o ∈ os, o.ResourceVersion' = u) ∨
    (∃ o : Obj, y.ErrMsg' = preMsgL x o ∧ (x.HasPreUID' && !decide (x.PreUID' = o.UID')) = false ∧
      o.ResourceVersion' = u)))

theorem opAnchors_of (A : List Nat) (x : Input) (y : Output)
    (h : ∀ u, OpReq x y u → uint.nat u ∈ A) : k8s_dist.OpAnchors A x y := by
  unfold k8s_dist.OpAnchors
  refine ⟨fun hc r hr => h r (Or.inl ⟨hc, hr⟩), fun r h1 h2 => h r (Or.inr (Or.inl ⟨h1, h2⟩)),
    fun hk hw evs hevs e he ht => h _ (Or.inr (Or.inr (Or.inl ⟨hk, hw, evs, hevs, e, he, ht, rfl⟩))),
    fun hk => ⟨h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inl rfl⟩))),
      h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inr (Or.inl rfl)⟩))),
      fun he => h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inr (Or.inr (Or.inl ⟨he, rfl⟩))⟩))),
      fun h4 he os hos o ho =>
        h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, he, os, hos, o, ho, rfl⟩)))⟩))),
      fun o hm hb =>
        h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inr (Or.inr (Or.inr (Or.inr ⟨o, hm, hb, rfl⟩)))⟩)))⟩⟩

/-- **The anchors from `all`'s keys** (the loop's invariant at its end, and the keys collected in
`anchors`) give `AnchorsOk`. -/
theorem anchorsOk_of (A : GMap w64 Bool) (l : List w64) (xs : List (Input × Output))
    (hl : ∀ k, k ∈ l ↔ (A !! k).isSome)
    (h : ∀ p ∈ xs, ∀ u, OpReq p.1 p.2 u → u = 0 ∨ (A !! u).isSome) :
    k8s_dist.AnchorsOk (0 :: l.map uint.nat) xs := by
  refine ⟨List.mem_cons_self .., fun p hp => opAnchors_of _ _ _ fun u hu => ?_⟩
  rcases h p hp u hu with rfl | hs
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem ((hl u).2 hs))

theorem hr_forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ i (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ t, i + 1, h1, h2 =>
    hr_forall₂_getElem t i (by simpa using h1) (by simpa using h2)

theorem hr_mem_take_succ {α : Type} {L : List α} {k : Nat} {a : α} (h : L[k]? = some a) {e : α}
    (he : e ∈ L.take (k + 1)) : e ∈ L.take k ∨ e = a := by
  rw [List.take_add_one, h] at he
  simpa using he

theorem take_succ_req {xs : List (Input × Output)} {j j' : Nat} {x : Input} {y : Output}
    {Pj Q : w64 → Prop} (hPj : (fun u => ∃ p ∈ xs.take j, OpReq p.1 p.2 u) = Pj)
    (hjx : xs.take j' = xs.take j ++ [(x, y)]) (hQ : ∀ u, Pj u → Q u)
    (hO : ∀ u, OpReq x y u → Q u) : ∀ u, (∃ p ∈ xs.take j', OpReq p.1 p.2 u) → Q u := by
  rintro u ⟨p, hp, hr⟩
  rw [hjx, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact hQ u (hPj ▸ ⟨p, hp, hr⟩)
  · exact hO u hr

/-- `A`'s keys are nonzero and it holds every nonzero `u` with `P u`. -/
def Good (P : w64 → Prop) (A : GMap w64 Bool) : Prop :=
  (∀ k, (A !! k).isSome → k ≠ 0) ∧ ∀ u, P u → u = 0 ∨ (A !! u).isSome

theorem good_mono {P Q : w64 → Prop} {A : GMap w64 Bool} (h : Good P A) (hq : ∀ u, Q u → P u) :
    Good Q A :=
  ⟨h.1, fun u hu => h.2 u (hq u hu)⟩

theorem good_ite {P : w64 → Prop} {A : GMap w64 Bool} (v : w64) (h : Good P A) :
    Good (fun u => P u ∨ u = v) (if v = W64 0 then A else <[v := true]> A) := by
  obtain ⟨hnz, hc⟩ := h
  by_cases hv : v = W64 0
  · rw [if_pos hv]
    refine ⟨hnz, fun u hu => hu.elim (hc u) (fun h => Or.inl ?_)⟩
    rw [h, hv]; rfl
  · rw [if_neg hv]
    refine ⟨fun k hk => ?_, fun u hu => ?_⟩
    · rcases (GMap.lookup_insert_is_Some A v k true).1 hk with rfl | ⟨_, hk⟩
      · exact hv
      · exact hnz k hk
    · rcases hu with hu | rfl
      · rcases hc u hu with h0 | hs
        · exact Or.inl h0
        · right
          exact (GMap.lookup_insert_is_Some A v u true).2 (by by_cases h : v = u <;> simp_all)
      · right; rw [GMap.lookup_insert]; rfl

/-- Every revision `HistoryRevs` may record for `(x, y)` (`opCost` of them). -/
def insL (x : Input) (y : Output) : List w64 :=
  [(parseRVD x.MinRV').getD 0, (parseRVD x.PreRV').getD 0, x.Cached'.ResourceVersion', y.ErrRV',
    y.ListRV', y.RV', rvOfMsgL y.ErrMsg'] ++
  ((decWEventsL y.WEvents').getD []).map (fun e => e.o.ResourceVersion') ++
  ((decItemRVsL y.Items').getD []).map (fun o => o.ResourceVersion')

theorem keys_ite_sub {S : w64 → Prop} {m : GMap w64 Bool} {v : w64} (hv : S v)
    (h : ∀ k, (m !! k).isSome → S k) :
    ∀ k, ((if v = W64 0 then m else <[v := true]> m) !! k).isSome → S k := by
  intro k hk
  by_cases h0 : v = W64 0
  · rw [if_pos h0] at hk; exact h k hk
  · rw [if_neg h0] at hk
    rcases (GMap.lookup_insert_is_Some m v k true).1 hk with rfl | ⟨_, hk⟩
    · exact hv
    · exact h k hk

theorem keys_insert_sub {S : w64 → Prop} {m : GMap w64 Bool} {v : w64} (hv : S v)
    (h : ∀ k, (m !! k).isSome → S k) : ∀ k, ((<[v := true]> m) !! k).isSome → S k := by
  intro k hk
  rcases (GMap.lookup_insert_is_Some m v k true).1 hk with rfl | ⟨_, hk⟩
  · exact hv
  · exact h k hk

theorem insL_length (x : Input) (y : Output) : (insL x y).length = opCost x y := by
  simp [insL, opCost]; omega

theorem histCost_eq (xs : List (Input × Output)) :
    (xs.flatMap fun p => insL p.1 p.2).length = histCost xs := by
  rw [List.length_flatMap]
  unfold histCost
  congr 1
  apply List.map_congr_left
  intro p _
  exact insL_length _ _

/-- A map whose keys are all in `L` has at most `L.length` of them. -/
theorem size_le_of_keys {V : Type} (m : GMap w64 V) (L : List w64)
    (h : ∀ k, (m !! k).isSome → k ∈ L) : GMap.size m ≤ L.length := by
  rw [GMap.size_eq_dom_list_length]
  exact List.Nodup.length_le_of_subset (GMap.nodup_dom_list m)
    (fun k hk => h k ((GMap.mem_dom_list m k).1 hk))

/-- `R0` with `k` set to the slice `so` holds, if any (a key's slice being built). -/
def withKey (R0 : GMap GoString GoSlice) (k : GoString) : Option GoSlice → GMap GoString GoSlice
  | none => R0
  | some c => <[k := c]> R0

theorem withKey_lookup {R0 : GMap GoString GoSlice} {k : GoString} (h : R0 !! k = none)
    (so : Option GoSlice) : ((withKey R0 k so) !! k).getD slice.nil = so.getD slice.nil := by
  cases so <;> simp [withKey, h]

theorem withKey_insert (R0 : GMap GoString GoSlice) (k : GoString) (so : Option GoSlice)
    (c : GoSlice) : <[k := c]> (withKey R0 k so) = withKey R0 k (some c) := by
  cases so <;> simp [withKey, GMap.insert_insert]

theorem withKey_keys {R0 : GMap GoString GoSlice} {k : GoString} {so : Option GoSlice}
    {P : GoString → Prop} (h : ∀ k', (R0 !! k').isSome → P k') (hk : P k) :
    ∀ k', ((withKey R0 k so) !! k').isSome → P k' := by
  intro k' hk'
  cases so with
  | none => exact h k' hk'
  | some c =>
    simp only [withKey, GMap.lookup_insert_eq_iff] at hk'
    by_cases e : k = k'
    · exact e ▸ hk
    · rw [if_neg e] at hk'; exact h k' hk'

theorem not_mem_take_of_getElem? {α : Type} {L : List α} {p : Nat} {a : α} (hnd : L.Nodup)
    (h : L[p]? = some a) : a ∉ L.take p := by
  intro hm
  have h2 : a ∈ L.drop p := List.mem_iff_getElem?.2 ⟨0, by rw [List.getElem?_drop]; simpa using h⟩
  rw [← List.take_append_drop p L] at hnd
  exact (List.nodup_append.1 hnd).2.2 a hm a h2 rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A `[]uint64` being built: its elements and its capacity owned. -/
def slOwn (s : GoSlice) : IProp GF :=
  iprop(∃ L : List w64, s ↦* L ∗ ownSliceCap w64 s (DFrac.own 1))

/-- A key's slice put back into the map being built. -/
theorem withKey_fold (R0 : GMap GoString GoSlice) (k : GoString) (so : Option GoSlice)
    (h : R0 !! k = none) :
    ([∗map] _k ↦ s ∈ R0, slOwn (GF := GF) s) ∗ slOwn (so.getD slice.nil) ⊢
      [∗map] _k ↦ s ∈ withKey R0 k so, slOwn s := by
  cases so with
  | none => simp only [withKey]; iintro ⟨H, -⟩; iexact H
  | some c =>
    simp only [withKey]
    iintro ⟨H, Hc⟩
    iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact h)).2
    iframe

/-- **The slices of a built map, chosen and made read-only**. -/
theorem slOwn_choose (R : GMap GoString GoSlice) :
    ([∗map] _k ↦ s ∈ R, slOwn (GF := GF) s) ⊢
      |==> ∃ f : GoString → List w64, ⌜∀ k, R !! k = none → f k = []⌝ ∗
        [∗map] k ↦ s ∈ R, s ↦*□ f k := by
  induction R using LawfulFiniteMap.induction_on with
  | hemp =>
    iintro -
    imodintro
    iexists fun _ => []
    isplitr
    · ipureintro; intro _ _; rfl
    iapply BigSepM.bigSepM_empty.2; iempintro
  | hins k0 s0 R' h ih =>
    iintro H
    icases (BigSepM.bigSepM_insert h).1 $$ H with ⟨H0, HR⟩
    imod ih $$ HR with ⟨%f, %Hf, HR⟩
    unfold slOwn
    icases H0 with ⟨%L, H0, -⟩
    imod ownSlice_persist _ _ _ $$ H0 with #H0
    imodintro
    iexists fun l => if l = k0 then L else f l
    isplitr
    · ipureintro
      intro k hk
      change (<[k0 := s0]> R') !! k = none at hk
      by_cases e : k = k0
      · rw [e, GMap.lookup_insert] at hk; cases hk
      · simp only [e, ↓reduceIte]
        exact Hf k (by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hk; exact hk)
    iapply (BigSepM.bigSepM_insert h).2
    simp only [↓reduceIte]
    iframe H0
    iapply (BigSepM.bigSepM_mono (fun {k x} hk => by
      have hne : k ≠ k0 := fun e => by subst e; rw [h] at hk; cases hk
      simp only [hne, ↓reduceIte]
      exact .rfl)) $$ HR

/-- The maps `all` (`am`) and `byKey` (`bm`), `all` holding every nonzero `u` with `P u`, and every
key of `all` and of `byKey`'s maps in `S` (the revisions the history may record: their number bounds
the maps' sizes). -/
def allSt (S : w64 → Prop) (am bm : GoMap) (P : w64 → Prop) : IProp GF :=
  iprop(∃ (A : GMap w64 Bool) (B : GMap GoString GoMap), am ↦$ A ∗ bm ↦$ B ∗
    ([∗map] _k ↦ l ∈ B, ∃ m : GMap w64 Bool, l ↦$ m ∗ ⌜∀ k, (m !! k).isSome → S k⌝) ∗
    ⌜Good P A ∧ ∀ k, (A !! k).isSome → S k⌝)

theorem allSt_mono (S : w64 → Prop) (am bm : GoMap) {P Q : w64 → Prop} (hq : ∀ u, Q u → P u) :
    allSt (GF := GF) S am bm P ⊢ allSt S am bm Q := by
  unfold allSt
  iintro ⟨%A, %B, HA, HB, HBs, %HG⟩
  iexists A, B
  iframe
  ipureintro
  exact ⟨good_mono HG.1 hq, HG.2⟩

theorem allSt_mono0 (S : w64 → Prop) (am bm : GoMap) {P Q : w64 → Prop}
    (hq : ∀ u, Q u → P u ∨ u = 0) :
    allSt (GF := GF) S am bm P ⊢ allSt S am bm Q := by
  unfold allSt
  iintro ⟨%A, %B, HA, HB, HBs, %HG⟩
  iexists A, B
  iframe
  ipureintro
  refine ⟨⟨HG.1.1, fun u hu => ?_⟩, HG.2⟩
  rcases hq u hu with h | h
  · exact HG.1.2 u h
  · exact Or.inl h

theorem HistoryRevs.wp_proof (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_rvOfMsg : rvOfMsg.spec (GF := GF) (hG := hG))
    (wp_decodeWEvents : decodeWEvents.spec (GF := GF) (hG := hG))
    (wp_decodeItemRVs : decodeItemRVs.spec (GF := GF) (hG := hG))
    (wp_Sort : _root_.Perennial.slices.Sort.spec (GF := GF) (hG := hG)) :
    HistoryRevs.spec (GF := GF) (hG := hG) := by
  intro sl ops xs dq Hops Hok Hcost
  generalize hS : (fun v : w64 => v ∈ xs.flatMap fun p => insL p.1 p.2) = S
  wp_start as Hs
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %am Ham
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := GoMap)) as %bm Hbm
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %wm Hwm
  (try wp_auto)
  ipersist all
  ipersist byKey
  generalize hfn : (func.mk BAnon (BNamed "rv") _ : GoFunc) = fn at *
  generalize hfo : (func.mk BAnon (BNamed "key") _ : GoFunc) = fo at *
  ihave #Hnum : iprop(∀ (v : w64) (A : GMap w64 Bool),
      {{ am ↦$ A }} (App (Val #fn) (Val #v))
      {{ RET #(); am ↦$ (if v = W64 0 then A else <[v := true]> A) }}) $$ []
  · iintro %v %A !> %Φ' HA HΦ'
    rw [← hfn, ← recv_eq_func_mk]
    wp_auto
    wp_if_destruct
    · iapply HΦ'
      iframe
    · wp_apply (wp_mapInsert go.uint64 am A v true) $$ HA as HA
      (try wp_auto)
      iapply HΦ'
      rw [if_neg Hif]
      iframe
  ihave #Hobj : iprop(∀ (key : GoString) (v : w64) (A : GMap w64 Bool) (B : GMap GoString GoMap),
      {{ ⌜S v⌝ ∗ am ↦$ A ∗ bm ↦$ B ∗
          [∗map] _k ↦ l ∈ B, ∃ m : GMap w64 Bool, l ↦$ m ∗ ⌜∀ k, (m !! k).isSome → S k⌝ }}
        (App (App (Val #fo) (Val #key)) (Val #v))
      {{ RET #(); am ↦$ (if v = W64 0 then A else <[v := true]> A) ∗
          ∃ B' : GMap GoString GoMap, bm ↦$ B' ∗
            [∗map] _k ↦ l ∈ B', ∃ m : GMap w64 Bool, l ↦$ m ∗ ⌜∀ k, (m !! k).isSome → S k⌝ }}) $$ []
  · iintro %key %v %A %B !> %Φ' ⟨%hSv, HA, HB, HBs⟩ HΦ'
    rw [← hfo, ← recv_eq_func_mk]
    wp_auto
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ'
      iframe
    wp_apply (wp_mapInsert go.uint64 am A v true) $$ HA as HA
    (try wp_auto)
    wp_apply (wp_map_lookup1 go.string (go.uint64.MapType go.bool) bm B key) $$ HB as HB
    (try wp_auto)
    rcases hBk : B !! key with _ | l0
    · rw [show ((none : Option GoMap).getD (zero_val GoMap)) = map.nil from rfl,
        decide_eq_true rfl]
      (try wp_auto)
      wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %l1 Hl1
      (try wp_auto)
      wp_apply (wp_mapInsert go.string bm B key l1) $$ HB as HB
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.string (go.uint64.MapType go.bool) bm _ key) $$ HB as HB
      (try rw [GMap.lookup_insert])
      (try wp_auto)
      wp_apply (wp_mapInsert go.uint64 l1 _ v true) $$ Hl1 as Hl1
      (try wp_auto)
      iapply HΦ'
      rw [if_neg Hif]
      iframe
      iapply (BigSepM.bigSepM_insert (Φ := fun (_ : GoString) (l : GoMap) =>
        iprop(∃ m : GMap w64 Bool, ownMap (GF := GF) l (DFrac.own 1) m ∗
          ⌜∀ k, (m !! k).isSome → S k⌝)) hBk).2
      iframe
      ipureintro
      exact keys_insert_sub hSv (fun k hk => by simp at hk)
    · ihave ⟨⟨%m0, Hl0, %Hm0⟩, HBs⟩ := (BigSepM.bigSepM_lookup_acc hBk).1 $$ HBs
      ihave %Hl0nn := ownMap_not_nil $$ Hl0
      rw [show ((some l0).getD (zero_val GoMap)) = l0 from rfl, decide_eq_false Hl0nn]
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.string (go.uint64.MapType go.bool) bm B key) $$ HB as HB
      rw [hBk, Option.getD_some]
      (try wp_auto)
      wp_apply (wp_mapInsert go.uint64 l0 m0 v true) $$ Hl0 as Hl0
      (try wp_auto)
      iapply HΦ'
      rw [if_neg Hif]
      iframe
      iapply HBs
      iexists _
      iframe
      ipureintro
      exact keys_insert_sub hSv Hm0
  ihave #Hnum' : iprop(∀ (v : w64) (P : w64 → Prop),
      {{ ⌜S v⌝ ∗ allSt S am bm P }} (App (Val #fn) (Val #v))
      {{ RET #(); allSt S am bm (fun u => P u ∨ u = v) }}) $$ []
  · iintro %v %P !> %Φ' ⟨%hSv, Hst⟩ HΦ'
    unfold allSt
    icases Hst with ⟨%A, %B, HA, HB, HBs, %HG⟩
    wp_apply Hnum $$ HA as HA
    iapply HΦ'
    iexists _, B
    iframe
    ipureintro
    exact ⟨good_ite v HG.1, keys_ite_sub hSv HG.2⟩
  ihave #Hobj' : iprop(∀ (key : GoString) (v : w64) (P : w64 → Prop),
      {{ ⌜S v⌝ ∗ allSt S am bm P }} (App (App (Val #fo) (Val #key)) (Val #v))
      {{ RET #(); allSt S am bm (fun u => P u ∨ u = v) }}) $$ []
  · iintro %key %v %P !> %Φ' ⟨%hSv, Hst⟩ HΦ'
    unfold allSt
    icases Hst with ⟨%A, %B, HA, HB, HBs, %HG⟩
    wp_apply Hobj $$ [HA HB HBs] as ⟨HA, %B', HB, HBs⟩
    · iframe
      ipureintro
      exact hSv
    iapply HΦ'
    iexists _, B'
    iframe
    ipureintro
    exact ⟨good_ite v HG.1, keys_ite_sub hSv HG.2⟩
  iclear Hnum Hobj
  clear hfn hfo
  ipersist obj
  ipersist num
  ipersist written
  ihave %Hlen := ownSlice_len $$ Hs
  ihave HI : (∃ (j : w64) (opv : github_com.anishathalye.porcupine.Operation) (W : GMap w64 Bool),
      "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ opv ∗ "Hwm" ∷ wm ↦$ W ∗
      "Hst" ∷ allSt S am bm (fun u => ∃ p ∈ xs.take (sint.nat j), OpReq p.1 p.2 u) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i op Hwm Ham Hbm]
  · iexists W64 0, _, _
    iframe
    isplitl
    · unfold allSt
      iexists ∅, ∅
      iframe
      isplitl
      · iapply BigSepM.bigSepM_empty.2
        itrivial
      ipureintro
      refine ⟨⟨fun k hk => by simp at hk, fun u hu => ?_⟩, fun k hk => by simp at hk⟩
      obtain ⟨p, hp, _⟩ := hu
      rw [show sint.nat (W64 0) = 0 by word] at hp
      simp at hp
    ipureintro
    constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len :=
      ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
    have h1 : sint.nat j < ops.length := by rw [Hlen.1]; word
    have h2 : sint.nat j < xs.length := Hops.length_eq ▸ h1
    have hR := hr_forall₂_getElem Hops (sint.nat j) h1 h2
    have hjx : xs.take (sint.nat (j + W64 1)) = xs.take (sint.nat j) ++ [xs[sint.nat j]] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one,
        List.getElem?_eq_getElem h2]
      rfl
    have hok := Hok _ (List.getElem_mem h2)
    have hmem := List.getElem_mem h2
    generalize xs[sint.nat j] = pj at hR hjx hok hmem
    obtain ⟨x, y⟩ := pj
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) ops dq (ops[sint.nat j]) Hj.1 $$ [Hs] as Hs
    · isplit
      · iexact Hs
      · ipureintro; exact List.getElem?_eq_getElem h1
    (try wp_auto)
    rw [hR.1]
    (try wp_auto)
    rw [hR.2]
    (try wp_auto)
    generalize hPj : (fun u => ∃ p ∈ xs.take (sint.nat j), OpReq p.1 p.2 u) = Pj
    wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt S am bm (fun u => Pj u ∨
        (MinOk x y ∧ parseRVD x.MinRV' = some u))) at next with [Hst «in» out] as ⟨«in», out, Hst⟩
    · wp_apply wp_parseRV as %n %err Hp
      rcases hd : parseRVD x.MinRV' with _ | m <;> isimp only [hd] at Hp
      · icases Hp with ⟨%hne, -, %h0⟩
        obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by cases err <;> simp_all
        (try wp_auto)
        wp_join_done
        (try iframe)
        iapply (allSt_mono S am bm (P := Pj)
          (fun u hu => by simpa using hu))
        iexact Hst
      · icases Hp with %h
        obtain ⟨rfl, rfl⟩ := h
        (try wp_auto)
        -- (G15) the MinRV is recorded unless the operation is not a watch and is answered tooLarge
        by_cases hk5 : x.Kind' = W64 5
        · simp only [hk5, _root_.decide_true]
          (try wp_auto)
          wp_apply Hnum' $$ [Hst] as Hst
          · iframe
            ipureintro
            refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
            simp [insL, *]
            (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
            (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
          (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono S am bm (P := fun u => Pj u ∨ u = n)
            (fun u hu => hu.imp id (fun h => (Option.some.inj h.2).symm)))
          iexact Hst
        · simp only [hk5, decide_false]
          (try wp_auto)
          by_cases h6 : y.Err' = W64 6
          · simp only [h6, _root_.decide_true, Bool.not_true]
            (try wp_auto)
            have hnmo : ¬MinOk x y := fun h => h.elim hk5 (fun h' => h' h6)
            wp_join_done
            (try iframe)
            iapply (allSt_mono S am bm (P := Pj)
              (fun u hu => hu.elim id (fun h => absurd h.1 hnmo)))
            iexact Hst
          · simp only [h6, decide_false, Bool.not_false]
            (try wp_auto)
            wp_apply Hnum' $$ [Hst] as Hst
            · iframe
              ipureintro
              refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
              simp [insL, *]
              (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
              (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
            (try wp_auto)
            wp_join_done
            (try iframe)
            iapply (allSt_mono S am bm (P := fun u => Pj u ∨ u = n)
              (fun u hu => hu.imp id (fun h => (Option.some.inj h.2).symm)))
            iexact Hst
    wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt S am bm (fun u => (Pj u ∨
        (MinOk x y ∧ parseRVD x.MinRV' = some u)) ∨ (x.HasPreRV' = true ∧ parseRVD x.PreRV' = some u)))
        at next with [Hst «in» out] as ⟨«in», out, Hst⟩
    · (try wp_auto)
      wp_apply wp_parseRV as %n %err Hp
      rcases hd : parseRVD x.PreRV' with _ | m <;> isimp only [hd] at Hp
      · icases Hp with ⟨%hne, -, %h0⟩
        obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by cases err <;> simp_all
        (try wp_auto)
        cases hb : x.HasPreRV' <;> (try wp_auto) <;> wp_join_done <;>
          (try iframe) <;>
          iapply (allSt_mono S am bm (P := fun u => Pj u ∨
            (MinOk x y ∧ parseRVD x.MinRV' = some u)) (fun u hu => by simpa using hu)) <;> iexact Hst
      · icases Hp with %h
        obtain ⟨rfl, rfl⟩ := h
        (try wp_auto)
        cases hb : x.HasPreRV'
        · (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono S am bm (P := fun u => Pj u ∨
            (MinOk x y ∧ parseRVD x.MinRV' = some u)) (fun u hu => by simpa using hu))
          iexact Hst
        · (try wp_auto)
          wp_apply Hnum' $$ [Hst] as Hst
          · iframe
            ipureintro
            refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
            simp [insL, *]
            (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
            (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
          (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono S am bm (P := fun u => (Pj u ∨
            (MinOk x y ∧ parseRVD x.MinRV' = some u)) ∨ u = n) (fun u hu => by simpa [eq_comm] using hu))
          iexact Hst
    generalize hP2 : (fun u => (Pj u ∨ (MinOk x y ∧ parseRVD x.MinRV' = some u)) ∨
      (x.HasPreRV' = true ∧ parseRVD x.PreRV' = some u)) = P2
    wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt S am bm P2)
        at next with [Hst «in» out] as ⟨«in», out, Hst⟩
    · (try wp_auto)
      cases hc : x.UseCached'
      · (try wp_auto)
        wp_join_done
      · (try wp_auto)
        wp_apply Hobj' $$ [Hst] as Hst
        · iframe
          ipureintro
          refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
          simp [insL, *]
          (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
          (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
        (try wp_auto)
        wp_join_done
        (try iframe)
        iapply (allSt_mono S am bm (P := fun u => P2 u ∨ u = x.Cached'.ResourceVersion')
          (fun u hu => Or.inl hu))
        iexact Hst
    wp_if_destruct
    · have hK := Hif
      wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt S am bm (fun u => P2 u ∨ (y.WFailed' = false ∧
          ∃ evs, decWEventsL y.WEvents' = some evs ∧ ∃ e ∈ evs, e.t < 4 ∧ e.o.ResourceVersion' = u)))
          at next with [Hst «in» out] as ⟨«in», out, Hst⟩
      · (try wp_auto)
        wp_apply wp_decodeWEvents as %esl %ok Hd
        rcases hd : decWEventsL y.WEvents' with _ | evs <;> isimp only [hd] at Hd
        · icases Hd with %hok
          subst hok
          (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono S am bm (P := P2) (fun u hu => by simpa using hu))
          iexact Hst
        icases Hd with ⟨%hok, Hd⟩
        iunfold wevsOwnM at Hd
        icases Hd with ⟨%ws, Hws, %hws⟩
        subst hok hws
        (try wp_auto)
        cases hw : y.WFailed'
        rotate_left
        · (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono S am bm (P := P2) (fun u hu => by simpa using hu))
          iexact Hst
        (try wp_auto)
        ihave %Hwl := ownSlice_len $$ Hws
        irename «in» => Hin
        ihave Hst := allSt_mono S am bm (Q := fun u => P2 u ∨
          ∃ e ∈ (ws.map wevOf).take (sint.nat (W64 0)), e.t < 4 ∧ e.o.ResourceVersion' = u)
          (fun u hu => hu.elim id (fun ⟨e, he, _⟩ => by
            rw [show sint.nat (W64 0) = 0 by word] at he; simp at he)) $$ Hst
        ihave HJ : (∃ (k : w64) (evv : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WEvent),
            "i" ∷ i_ptr ↦ k ∗ "ev" ∷ ev_ptr ↦ evv ∗ "Hws" ∷ esl ↦* ws ∗
            "Hst" ∷ allSt S am bm (fun u => P2 u ∨
              ∃ e ∈ (ws.map wevOf).take (sint.nat k), e.t < 4 ∧ e.o.ResourceVersion' = u) ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z esl.len⌝ : IProp GF) $$ [i ev Hws Hst]
        · iexists W64 0, _
          iframe
          ipureintro
          constructor <;> word
        wp_for HJ
        wp_if_destruct
        · have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z esl.len :=
            ⟨Hk.1, by first | exact Hif | exact dec_true Hif⟩
          list_elem ws (sint.nat k) as w
          simp only [Hb', _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index esl (sint.Z k) ws _ w Hk.1 $$ [Hws] as Hws
          · isplit
            · iexact Hws
            · ipureintro; exact Hw_lookup
          have hl : (ws.map wevOf)[sint.nat k]? = some (wevOf w) := by simp [Hw_lookup]
          have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
          have hstep : ∀ u, (P2 u ∨ ∃ e ∈ (ws.map wevOf).take (sint.nat (k + W64 1)),
                e.t < 4 ∧ e.o.ResourceVersion' = u) →
              (P2 u ∨ ∃ e ∈ (ws.map wevOf).take (sint.nat k), e.t < 4 ∧ e.o.ResourceVersion' = u) ∨
                (uint.nat w.Type' < 4 ∧ u = w.Obj'.ResourceVersion') := by
            intro u hu
            rcases hu with h | ⟨e, he, ht, hrv⟩
            · exact Or.inl (Or.inl h)
            rw [hk1] at he
            rcases hr_mem_take_succ hl he with he' | rfl
            · exact Or.inl (Or.inr ⟨e, he', ht, hrv⟩)
            · exact Or.inr ⟨ht, hrv.symm⟩
          (try wp_auto)
          wp_if_destruct
          · wp_apply Hnum' $$ [Hst] as Hst
            · iframe
              ipureintro
              refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
              simp [insL, *]
              (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
              (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
            ihave Hst := allSt_mono S am bm (fun u hu => (hstep u hu).imp id (fun h => h.2)) $$ Hst
            wp_for_post
            iframe
            iexists k + W64 1, w
            iframe
            ipureintro
            constructor <;> word
          (try wp_auto)
          wp_if_destruct
          · wp_apply Hobj' $$ [Hst] as Hst
            · iframe
              ipureintro
              refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
              simp [insL, *]
              (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
              (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
            ihave Hst := allSt_mono S am bm (fun u hu => (hstep u hu).imp id (fun h => h.2)) $$ Hst
            wp_for_post
            iframe
            iexists k + W64 1, w
            iframe
            ipureintro
            constructor <;> word
          · ihave Hst := allSt_mono S am bm (fun u hu => (hstep u hu).elim id
              (fun h => absurd h.1 (by word))) $$ Hst
            wp_for_post
            iframe
            iexists k + W64 1, w
            iframe
            ipureintro
            constructor <;> word
        · have hge : ¬ sint.Z k < sint.Z esl.len := by first | exact Hif | exact dec_false Hif
          (try rw [decide_eq_false hge, if_pos (decide_eq_true rfl)])
          (try wp_auto)
          have hfull : (ws.map wevOf).take (sint.nat k) = ws.map wevOf :=
            List.take_of_length_le (by simp; word)
          wp_join_done
          (try iframe)
          iapply (allSt_mono S am bm (P := fun u => P2 u ∨
            ∃ e ∈ (ws.map wevOf).take (sint.nat k), e.t < 4 ∧ e.o.ResourceVersion' = u)
            (fun u hu => hu.imp id (fun ⟨_, evs, he, h⟩ => by
            simp only [Option.some.injEq] at he; subst he; rw [hfull]; exact h)))
          iexact Hst
      wp_for_post
      iframe
      iexists j + W64 1, _, W
      iframe
      isplitl
      · have hfin : ∀ u, (∃ p ∈ xs.take (sint.nat (j + W64 1)), OpReq p.1 p.2 u) →
            P2 u ∨ (y.WFailed' = false ∧ ∃ evs, decWEventsL y.WEvents' = some evs ∧
              ∃ e ∈ evs, e.t < 4 ∧ e.o.ResourceVersion' = u) := by
          refine take_succ_req hPj hjx (fun u h => by rw [← hP2]; exact Or.inl (Or.inl (Or.inl h)))
            (fun u hu => ?_)
          rw [← hP2]
          rcases hu with h | h | h | ⟨hk5, _⟩
          · exact Or.inl (Or.inl (Or.inr h))
          · exact Or.inl (Or.inr h)
          · obtain ⟨_, hw, evs, he, e, hm, ht⟩ := h
            exact Or.inr ⟨hw, evs, he, e, hm, ht.1, ht.2⟩
          · exact absurd hK hk5
        iapply (allSt_mono S am bm hfin)
        iexact Hst
      ipureintro
      constructor <;> word
    · have hK := Hif
      wp_apply Hnum' $$ [Hst] as Hst
      · iframe
        ipureintro
        refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
        simp [insL, *]
        (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
        (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
      (try wp_auto)
      wp_apply Hnum' $$ [Hst] as Hst
      · iframe
        ipureintro
        refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
        simp [insL, *]
        (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
        (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
      (try wp_auto)
      wp_apply wp_rvOfMsg
      (try wp_auto)
      ipersist r
      wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt S am bm (fun u => ((P2 u ∨ u = y.ErrRV') ∨
          u = y.ListRV') ∨ u = rvOfMsgL y.ErrMsg')) at next with [Hst «in» out] as ⟨«in», out, Hst⟩
      · (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono0 S am bm (P := fun u => (P2 u ∨ u = y.ErrRV') ∨ u = y.ListRV')
            (fun u hu => hu.imp id (fun h => h.trans Hif)))
          iexact Hst
        · (try wp_auto)
          wp_apply Hobj' $$ [Hst] as Hst
          · iframe
            ipureintro
            refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
            simp [insL, *]
            (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
            (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
          (try wp_auto)
          wp_join_done
      generalize hP3 : (fun u => ((P2 u ∨ u = y.ErrRV') ∨ u = y.ListRV') ∨ u = rvOfMsgL y.ErrMsg') = P3
      wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ (∃ W' : GMap w64 Bool, wm ↦$ W') ∗
          allSt S am bm (fun u => P3 u ∨ (y.Err' = W64 0 ∧ u = y.RV')))
          at next with [Hst «in» out Hwm] as ⟨«in», out, ⟨%W1, Hwm⟩, Hst⟩
      · (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_apply Hobj' $$ [Hst] as Hst
          · iframe
            ipureintro
            refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
            simp [insL, *]
            (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
            (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
          (try wp_auto)
          ihave Hst := allSt_mono S am bm (P := fun u => P3 u ∨ u = y.RV')
            (Q := fun u => P3 u ∨ (y.Err' = W64 0 ∧ u = y.RV')) (fun u hu => hu.imp id (fun h => h.2)) $$ Hst
          repeat' (wp_if_destruct <;> (try wp_auto))
          all_goals (try (cases hn : x.NoOp' <;> simp only [Bool.not_true, Bool.not_false] <;>
            (try wp_auto)))
          all_goals first
            | (wp_join_done; done)
            | (wp_apply (wp_mapInsert go.uint64 wm W y.RV' true) $$ Hwm as Hwm
               (try wp_auto)
               wp_join_done)
        · (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono S am bm (P := P3) (fun u hu => hu.elim id (fun h => absurd h.1 Hif)))
          iexact Hst
      generalize hP4 : (fun u => P3 u ∨ (y.Err' = W64 0 ∧ u = y.RV')) = P4
      have hfin : ∀ u, (∃ p ∈ xs.take (sint.nat (j + W64 1)), OpReq p.1 p.2 u) →
          P4 u ∨ (x.Kind' = W64 4 ∧ y.Err' = W64 0 ∧
            ∃ ds, decItemRVsL y.Items' = some ds ∧ ∃ d ∈ ds, d.ResourceVersion' = u) := by
        refine take_succ_req hPj hjx (fun u h => ?_) (fun u hu => ?_)
        · subst hP4 hP3 hP2
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
        subst hP4 hP3 hP2
        rcases hu with h | h | h | ⟨_, h | h | ⟨he, h⟩ | ⟨h4, he, os, hos, o, ho, hrv⟩ | ⟨o, hm, hb, hrv⟩⟩
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
        · exact absurd h.1 hK
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
        · exact Or.inl (Or.inr ⟨he, h⟩)
        · obtain ⟨hs, hl⟩ := hok.2 h4 he
          rw [hos] at hs hl
          obtain ⟨ds, hds, hmap⟩ := decItemRVsL_encItemsL os hl hs
          have hm : u ∈ ds.map (·.ResourceVersion') := by
            rw [hmap]; exact List.mem_map.2 ⟨o, ho, hrv⟩
          obtain ⟨d, hd, hdu⟩ := List.mem_map.1 hm
          exact Or.inr ⟨h4, he, ds, hos ▸ hds, d, hd, hdu⟩
        · refine Or.inl (Or.inl (Or.inr ?_))
          rw [hm, rvOfMsgL_preMsgL x o hok.1 hb]
          exact hrv.symm
      (try wp_auto)
      wp_if_destruct
      rotate_left
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, W1
        iframe
        isplitl
        · iapply (allSt_mono S am bm (P := P4) (fun u hu => (fun u hu => hu.elim id (fun h => absurd h.1 Hif)) u (hfin u hu)))
          iexact Hst
        ipureintro
        constructor <;> word
      have hK4 := Hif
      (try wp_auto)
      wp_if_destruct
      rotate_left
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, W1
        iframe
        isplitl
        · iapply (allSt_mono S am bm (P := P4) (fun u hu => (fun u hu => hu.elim id (fun h => absurd h.2.1 Hif)) u (hfin u hu)))
          iexact Hst
        ipureintro
        constructor <;> word
      have hE0 := Hif
      (try wp_auto)
      wp_apply wp_decodeItemRVs as %isl %ok Hd
      rcases hd : decItemRVsL y.Items' with _ | ds <;> isimp only [hd] at Hd
      · icases Hd with %hok
        subst hok
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, W1
        iframe
        isplitl
        · iapply (allSt_mono S am bm (P := P4) (fun u hu => (fun u hu => by simpa [hd] using hu) u (hfin u hu)))
          iexact Hst
        ipureintro
        constructor <;> word
      icases Hd with ⟨%hok, Hws⟩
      subst hok
      (try wp_auto)
      ihave %Hwl := ownSlice_len $$ Hws
      ihave Hst := allSt_mono S am bm (Q := fun u => P4 u ∨
        ∃ e ∈ ds.take (sint.nat (W64 0)), e.ResourceVersion' = u)
        (fun u hu => hu.elim id (fun ⟨e, he, _⟩ => by
          rw [show sint.nat (W64 0) = 0 by word] at he; simp at he)) $$ Hst
      ihave HJ : (∃ (k : w64) (itv : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.item),
          "i" ∷ i_ptr ↦ k ∗ "it" ∷ it_ptr ↦ itv ∗
          "Hws" ∷ isl ↦* ds.map (fun o => github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.item.mk (objKeyL o) o false) ∗
          "Hst" ∷ allSt S am bm (fun u => P4 u ∨
            ∃ e ∈ ds.take (sint.nat k), e.ResourceVersion' = u) ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z isl.len⌝ : IProp GF) $$ [i it Hws Hst]
      · iexists W64 0, _
        iframe
        ipureintro
        constructor <;> word
      wp_for HJ
      wp_if_destruct
      · have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z isl.len :=
          ⟨Hk.1, by first | exact Hif | exact dec_true Hif⟩
        have hkl : sint.nat k < ds.length := by simp at Hwl; word
        have hl : ds[sint.nat k]? = some ds[sint.nat k] := List.getElem?_eq_getElem hkl
        generalize ds[sint.nat k] = d at hl
        simp only [Hb', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index isl (sint.Z k) _ _ (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.item.mk (objKeyL d) d false) Hk.1 $$ [Hws]
          as Hws
        · isplit
          · iexact Hws
          · ipureintro; simp [hl]
        have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        have hstep : ∀ u, (P4 u ∨ ∃ e ∈ ds.take (sint.nat (k + W64 1)), e.ResourceVersion' = u) →
            (P4 u ∨ ∃ e ∈ ds.take (sint.nat k), e.ResourceVersion' = u) ∨ u = d.ResourceVersion' := by
          intro u hu
          rcases hu with h | ⟨e, he, hrv⟩
          · exact Or.inl (Or.inl h)
          rw [hk1] at he
          rcases hr_mem_take_succ hl he with he' | rfl
          · exact Or.inl (Or.inr ⟨e, he', hrv⟩)
          · exact Or.inr hrv.symm
        (try wp_auto)
        wp_apply Hobj' $$ [Hst] as Hst
        · iframe
          ipureintro
          refine hS ▸ List.mem_flatMap.2 ⟨_, hmem, ?_⟩
          simp [insL, *]
          (try (right; right; right; right; right; right; right; left; exact ⟨_, List.mem_of_getElem? Hw_lookup, rfl⟩))
          (try (right; right; right; right; right; right; right; right; exact ⟨_, List.mem_of_getElem? hl, rfl⟩))
        ihave Hst := allSt_mono S am bm hstep $$ Hst
        wp_for_post
        iframe
        iexists k + W64 1, _
        iframe
        ipureintro
        constructor <;> word
      · have hge : ¬ sint.Z k < sint.Z isl.len := by first | exact Hif | exact dec_false Hif
        (try rw [decide_eq_false hge, if_pos (decide_eq_true rfl)])
        (try wp_auto)
        have hfull : ds.take (sint.nat k) = ds := List.take_of_length_le (by simp at Hwl; word)
        wp_for_post
        iframe
        iexists j + W64 1, _, W1
        iframe
        isplitl
        · iapply (allSt_mono S am bm (P := fun u => P4 u ∨
          ∃ e ∈ ds.take (sint.nat k), e.ResourceVersion' = u) (fun u hu => (fun u hu => hu.imp id (fun ⟨_, _, ds', he, h⟩ => by
            rw [hd] at he; simp only [Option.some.injEq] at he; subst he; rw [hfull]; exact h)) u (hfin u hu)))
          iexact Hst
        ipureintro
        constructor <;> word
  · have hge : ¬ sint.Z j < sint.Z sl.len := by first | exact Hif | exact dec_false Hif
    have hfull : xs.take (sint.nat j) = xs := List.take_of_length_le (by rw [← Hops.length_eq, Hlen.1]; word)
    unfold allSt
    icases Hst with ⟨%A, %B, HA, HB, HBs, %HG⟩
    rw [hfull] at HG
    ihave %Hrnn := typedPointsto_not_null $$ r
    iStructNamed r
    have hSL : ∀ k, S k → k ∈ xs.flatMap fun p => insL p.1 p.2 := fun k hk => by rw [← hS] at hk; exact hk
    have hNA : GMap.size A ≤ 2 ^ 62 := by
      have h := size_le_of_keys A _ (fun k hk => hSL k (HG.2 k hk))
      rw [histCost_eq] at h; omega
    ihave Hn := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
    ihave Hc := ownSliceCap_nil (V := w64) (GF := GF)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List w64) (p : Int) => iprop(∃ (x : w64) (s : GoSlice),
        "%Hp" ∷ ⌜0 ≤ p⌝ ∗ "v" ∷ v_ptr ↦ x ∗ "anchors" ∷ r_ptr.[Revs, go!"anchors"] ↦ s ∗
        "Hsl" ∷ s ↦* keys.take p.toNat ∗ "Hcap" ∷ ownSliceCap w64 s (DFrac.own 1))) $$ HA
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [v anchors Hn Hc]
    · iexists _, slice.nil
      simp only [named, Int.toNat_zero, List.take_zero]
      iframe
      isplitr
      · ipureintro; exact Int.le_refl _
      isplitl [Hn]
      · iexact Hn
      · iexact Hc
    isplitr
    · imodintro
      iintro %p %k %o ⟨%Hkey, %Ho⟩ HP
      iNamed HP
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_slice_append_dfrac $$ [$Hsl $Hcap $Hl1]
        as %sl' ⟨Hsl, Hcap, -⟩
      · ipureintro; exact DFrac.valid_own_one
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists k, sl'
      simp only [named]
      have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [k] := by
        rw [show (p + 1).toNat = p.toNat + 1 by omega]
        rw [List.take_add_one, Hkey]; rfl
      rw [Htake]
      iframe
      ipureintro; omega
    iintro HP HA
    iNamed HP
    rw [← Hklen, Int.toNat_natCast, List.take_length]
    wp_auto
    ihave #Hless := _root_.Perennial.slices.lessImplements_uint64 (GF := GF)
    wp_apply wp_Sort (fun (x y : w64) => uint.Z x < uint.Z y) s keys
        _root_.Perennial.slices.StrictWeakOrder_unsigned_lt $$ [Hsl]
      with %ks' ⟨Hsl, %Hperm, %Hsorted⟩
    · iframe Hsl; iframe #; ipureintro; rw [Hklen]; exact hNA
    -- the two maps of `r`
    wp_apply (wp_map_make1 (K := GoString) (V := GoSlice)) as %rb Hrb
    (try wp_auto)
    wp_apply (wp_map_make1 (K := GoString) (V := GoSlice)) as %rf Hrf
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (bks : List GoString) (p : Int) => iprop(
        ∃ (RB RF : GMap GoString GoSlice) (mv : GoMap) (kv : GoString),
        "%Hp" ∷ ⌜0 ≤ p⌝ ∗ "m" ∷ m_ptr ↦ mv ∗ "k" ∷ k_ptr ↦ kv ∗
        "Hrb" ∷ rb ↦$ RB ∗ "HRB" ∷ ([∗map] _k ↦ s ∈ RB, slOwn s) ∗
        "Hrf" ∷ rf ↦$ RF ∗ "HRF" ∷ ([∗map] _k ↦ s ∈ RF, slOwn s) ∗
        "%HRBk" ∷ ⌜∀ k, (RB !! k).isSome → k ∈ bks.take p.toNat⌝ ∗
        "%HRFk" ∷ ⌜∀ k, (RF !! k).isSome → k ∈ bks.take p.toNat⌝ ∗
        "HBs" ∷ ([∗map] _k ↦ l ∈ B, ∃ m : GMap w64 Bool, l ↦$ m ∗ ⌜∀ k, (m !! k).isSome → S k⌝) ∗
        "Hwm" ∷ wm ↦$ W ∗ "byKey" ∷ r_ptr.[Revs, go!"byKey"] ↦ rb ∗
        "fastByKey" ∷ r_ptr.[Revs, go!"fastByKey"] ↦ rf)) $$ HB
    iintro %bks ⟨%Hbset, %Hblen, %Hbnodup⟩
    isplitl [m k Hrb Hrf HBs Hwm byKey fastByKey]
    · iexists ∅, ∅, _, _
      simp only [named]
      iframe
      isplitr
      · ipureintro; exact Int.le_refl _
      isplitl
      · iapply BigSepM.bigSepM_empty.2; iempintro
      isplitl
      · iapply BigSepM.bigSepM_empty.2; iempintro
      ipureintro
      constructor <;> (intro _ h; simp at h)
    isplitr
    · imodintro
      iintro %p %key %o ⟨%Hkey, %Ho⟩ HP
      iNamed HP
      wp_auto
      have hRBn : RB !! key = none := by
        cases hh : RB !! key with
        | none => rfl
        | some _ => exact absurd (HRBk key (by rw [hh]; rfl)) (not_mem_take_of_getElem? Hbnodup Hkey)
      have hRFn : RF !! key = none := by
        cases hh : RF !! key with
        | none => rfl
        | some _ => exact absurd (HRFk key (by rw [hh]; rfl)) (not_mem_take_of_getElem? Hbnodup Hkey)
      icases (BigSepM.bigSepM_lookup_acc (by rw [gmap_get?_eq]; exact Ho)).1 $$ HBs with ⟨Hom, HBclose⟩
      icases Hom with ⟨%mm, Hmm, %Hmmk⟩
      have hNm : GMap.size mm ≤ 2 ^ 62 := by
        have h := size_le_of_keys mm _ (fun k hk => hSL k (Hmmk k hk))
        rw [histCost_eq] at h; omega
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (iks : List w64) (i : Int) => iprop(
          ∃ (sb sf : Option GoSlice) (x : w64) (Lb Lf : List w64),
          "%Hi" ∷ ⌜0 ≤ i⌝ ∗ "v" ∷ v_ptr ↦ x ∗ "k" ∷ k_ptr ↦ key ∗
          "Hrb" ∷ rb ↦$ withKey RB key sb ∗ "Hb" ∷ sb.getD slice.nil ↦* Lb ∗
          "Hbc" ∷ ownSliceCap w64 (sb.getD slice.nil) (DFrac.own 1) ∗ "%HLb" ∷ ⌜Lb.length ≤ i.toNat⌝ ∗
          "Hrf" ∷ rf ↦$ withKey RF key sf ∗ "Hf" ∷ sf.getD slice.nil ↦* Lf ∗
          "Hfc" ∷ ownSliceCap w64 (sf.getD slice.nil) (DFrac.own 1) ∗ "%HLf" ∷ ⌜Lf.length ≤ i.toNat⌝ ∗
          "Hwm" ∷ wm ↦$ W ∗ "byKey" ∷ r_ptr.[Revs, go!"byKey"] ↦ rb ∗
          "fastByKey" ∷ r_ptr.[Revs, go!"fastByKey"] ↦ rf)) $$ Hmm
      iintro %iks ⟨%Hiset, %Hilen, %Hinodup⟩
      isplitl [v k Hrb Hrf Hwm byKey fastByKey]
      · iexists none, none, _, [], []
        simp only [named, withKey, Option.getD_none]
        iframe
        isplitr
        · ipureintro; exact Int.le_refl _
        iframe #
        ipureintro; constructor <;> simp
      isplitr
      · imodintro
        iintro %i %vk %bv ⟨%Hvk, %Hbv⟩ HP
        iNamed HP
        wp_auto
        wp_apply (wp_map_lookup1 go.string go.uint64.SliceType rb (withKey RB key sb) key
          (DFrac.own 1)) $$ Hrb as Hrb
        rw [show (zero_val GoSlice) = slice.nil from rfl, withKey_lookup hRBn]
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %l1 ⟨Hl1, -⟩
        simp only [go.arrayLiteralSize, List.foldl]
        (try wp_auto)
        wp_apply wp_slice_append_dfrac $$ [$Hb $Hbc $Hl1] as %sb' ⟨Hb, Hbc, -⟩
        · ipureintro; exact DFrac.valid_own_one
        (try wp_auto)
        wp_apply (wp_mapInsert go.string rb (withKey RB key sb) key sb') $$ Hrb as Hrb
        rw [withKey_insert]
        (try wp_auto)
        wp_apply (wp_map_lookup1 go.uint64 go.bool wm W vk (DFrac.own 1)) $$ Hwm as Hwm
        (try wp_auto)
        generalize (W !! vk).getD (zero_val Bool) = wb
        cases wb <;> simp only [Bool.not_true, Bool.not_false]
        · (try wp_auto)
          wp_apply (wp_map_lookup1 go.string go.uint64.SliceType rf (withKey RF key sf) key
            (DFrac.own 1)) $$ Hrf as Hrf
          rw [show (zero_val GoSlice) = slice.nil from rfl, withKey_lookup hRFn]
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %l2 ⟨Hl2, -⟩
          simp only [go.arrayLiteralSize, List.foldl]
          (try wp_auto)
          wp_apply wp_slice_append_dfrac $$ [$Hf $Hfc $Hl2] as %sf' ⟨Hf, Hfc, -⟩
          · ipureintro; exact DFrac.valid_own_one
          (try wp_auto)
          wp_apply (wp_mapInsert go.string rf (withKey RF key sf) key sf') $$ Hrf as Hrf
          rw [withKey_insert]
          (try wp_auto)
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists (some sb'), (some sf'), vk, _, _
          simp only [named, Option.getD_some]
          iframe
          ipureintro
          refine ⟨by omega, ?_, ?_⟩ <;> (try simp) <;> omega
        · (try wp_auto)
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists (some sb'), sf, vk, _, Lf
          simp only [named, Option.getD_some]
          iframe
          ipureintro
          refine ⟨by omega, ?_, ?_⟩ <;> (try simp) <;> omega
      iintro HP Hmm
      iNamed HP
      wp_auto
      wp_apply (wp_map_lookup1 go.string go.uint64.SliceType rb (withKey RB key sb) key
        (DFrac.own 1)) $$ Hrb as Hrb
      rw [show (zero_val GoSlice) = slice.nil from rfl, withKey_lookup hRBn]
      (try wp_auto)
      wp_apply wp_Sort (fun (x y : w64) => uint.Z x < uint.Z y) (sb.getD slice.nil) Lb
          _root_.Perennial.slices.StrictWeakOrder_unsigned_lt $$ [Hb]
        with %Lb' ⟨Hb, -, -⟩
      · iframe Hb; iframe #; ipureintro; omega
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.string go.uint64.SliceType rf (withKey RF key sf) key
        (DFrac.own 1)) $$ Hrf as Hrf
      rw [show (zero_val GoSlice) = slice.nil from rfl, withKey_lookup hRFn]
      (try wp_auto)
      wp_apply wp_Sort (fun (x y : w64) => uint.Z x < uint.Z y) (sf.getD slice.nil) Lf
          _root_.Perennial.slices.StrictWeakOrder_unsigned_lt $$ [Hf]
        with %Lf' ⟨Hf, -, -⟩
      · iframe Hf; iframe #; ipureintro; omega
      (try wp_auto)
      ihave HBs := HBclose $$ [Hmm]
      · iexists mm; iframe; ipureintro; exact Hmmk
      ihave HRB := withKey_fold RB key sb hRBn $$ [HRB Hb Hbc]
      · isplitl [HRB]
        · iexact HRB
        simp only [slOwn]; iexists Lb'; iframe
      ihave HRF := withKey_fold RF key sf hRFn $$ [HRF Hf Hfc]
      · isplitl [HRF]
        · iexact HRF
        simp only [slOwn]; iexists Lf'; iframe
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists (withKey RB key sb), (withKey RF key sf), o, key
      simp only [named]
      iframe
      ipureintro
      have Htake : bks.take (p + 1).toNat = bks.take p.toNat ++ [key] := by
        rw [show (p + 1).toNat = p.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
      rw [Htake]
      refine ⟨by omega,
        withKey_keys (fun k hk => List.mem_append_left _ (HRBk k hk))
          (List.mem_append_right _ (List.mem_singleton_self _)),
        withKey_keys (fun k hk => List.mem_append_left _ (HRFk k hk))
          (List.mem_append_right _ (List.mem_singleton_self _))⟩
    iintro HP HB
    iNamed HP
    ihave Hr : r_ptr ↦ Revs.mk s rb rf $$ [anchors byKey fastByKey]
    · iapply typedPointsto_combine _ _ _ Hrnn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    imod slOwn_choose RB $$ HRB with ⟨%fb, %Hfb, #HRB⟩
    imod slOwn_choose RF $$ HRF with ⟨%ff, %Hff, #HRF⟩
    imod ownMap_persist $$ Hrb with #Hrb
    imod ownMap_persist $$ Hrf with #Hrf
    imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    wp_auto
    have hmem : ∀ k, k ∈ ks' ↔ (A !! k).isSome := fun k => Hperm.mem_iff.symm.trans (Hkset k)
    have hpw : ks'.Pairwise (fun a b => uint.nat a < uint.nat b) := by
      have hnd : ks'.Nodup := Hperm.nodup_iff.1 Hknodup
      have hle : ks'.Pairwise (fun a b => uint.Z a ≤ uint.Z b) := by
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        have := Hsorted i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
        omega
      exact (hle.and hnd).imp (fun {a b} h => by
        obtain ⟨h1, h2⟩ := h
        have h3 : uint.Z a ≠ uint.Z b := fun e => h2 (by word)
        word)
    iapply HΦ
    iframe Hs
    iexists ⟨ks', fb, ff⟩
    isplitr
    · simp only [revsOwn, keyRevsOwn]
      iframe Hsl
      isplitr
      · ipureintro; exact hpw
      isplitr
      · iexists RB; iframe #; ipureintro; exact Hfb
      · iexists RF; iframe #; ipureintro; exact Hff
    · ipureintro
      exact ⟨fun a ha => HG.1.1 a ((hmem a).1 ha),
        anchorsOk_of A ks' xs hmem (fun p hp u hu => HG.1.2 u ⟨p, hp, hu⟩)⟩

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
