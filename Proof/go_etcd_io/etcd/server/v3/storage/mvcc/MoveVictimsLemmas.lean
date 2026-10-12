/-
Lemmas of `watchableStore.moveVictims`'s proof (`watchableStore__moveVictims.lean`): big
separating conjunctions over filtered, united and mapped maps, the agreement and exclusivity of a
watcher's state fields, and the lock's state transitions of the victims' mover: the victims taken
out (`takeState`), a watcher whose batch was sent put back (`readdState`), the failed ones made
victims again in one batch (`appendState`), with their invariants (`WsOk`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchFrac

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section generic
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mv_bigSepM_sep {V : Type} (Φ Ψ : Loc → V → IProp GF) (m : GMap Loc V) :
    ([∗map] k ↦ v ∈ m, Φ k v ∗ Ψ k v) ⊣⊢ ([∗map] k ↦ v ∈ m, Φ k v) ∗ [∗map] k ↦ v ∈ m, Ψ k v := by
  rw [BigSepM.bigSepM_sep_eq]; exact .rfl

theorem mv_std_delete_eq {V : Type} (m : GMap Loc V) (k : Loc) : Std.delete m k = GMap.delete k m :=
  rfl

theorem mv_gfilter_eq {V : Type} (p : Loc → V → Bool) (m : GMap Loc V) :
    Iris.Std.PartialMap.filter p m = GMap.filter p m := by
  apply GMap.ext; intro k
  show (m !! k).bind (fun v => if p k v then some v else none) = (m !! k).filter (p k)
  cases m !! k <;> simp [Option.filter]

theorem mv_bigSepM_split {V : Type} (Φ : Loc → V → IProp GF) (p : Loc → V → Bool) (m : GMap Loc V) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊣⊢
      ([∗map] k ↦ v ∈ GMap.filter p m, Φ k v) ∗ ([∗map] k ↦ v ∈ GMap.filter (fun k v => !p k v) m, Φ k v) := by
  rw [← mv_gfilter_eq, ← mv_gfilter_eq, BigSepM.bigSepM_filter_cond, BigSepM.bigSepM_filter_cond,
    ← BigSepM.bigSepM_sep_eq]
  constructor
  · refine BigSepM.bigSepM_mono (fun {k v} _ => ?_)
    cases p k v <;> simp only [Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, ite_false]
    · iintro H; isplitl []
      · iempintro
      iexact H
    · iintro H; iframe H
  · refine BigSepM.bigSepM_mono (fun {k v} _ => ?_)
    cases p k v <;> simp only [Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, ite_false]
    · iintro ⟨-, H⟩; iexact H
    · iintro ⟨H, -⟩; iexact H

/-- A disjoint union of maps. -/
theorem mv_bigSepM_union {V : Type} (Φ : Loc → V → IProp GF) (m1 m2 : GMap Loc V)
    (hd : ∀ k, (m1 !! k).isSome → m2 !! k = none) :
    ([∗map] k ↦ v ∈ m1 ∪ m2, Φ k v) ⊣⊢ ([∗map] k ↦ v ∈ m1, Φ k v) ∗ ([∗map] k ↦ v ∈ m2, Φ k v) := by
  have h1 : GMap.filter (fun k _ => (m1 !! k).isSome) (m1 ∪ m2) = m1 := by
    apply GMap.ext; intro k
    show ((m1 ∪ m2) !! k).filter _ = m1 !! k
    rw [GMap.lookup_union]; cases h : m1 !! k <;> cases h' : m2 !! k <;> simp [h, Option.filter]
  have h2 : GMap.filter (fun k v => !(fun k _ => (m1 !! k).isSome) k v) (m1 ∪ m2) = m2 := by
    apply GMap.ext; intro k
    show ((m1 ∪ m2) !! k).filter _ = m2 !! k
    rw [GMap.lookup_union]; cases h : m1 !! k
    · simp [h]; cases m2 !! k <;> simp
    · have := hd k (by rw [h]; rfl); simp [h, this, Option.filter]
  refine (mv_bigSepM_split Φ (fun k _ => (m1 !! k).isSome) (m1 ∪ m2)).trans ?_
  rw [h1, h2]
  exact .rfl

/-- A map's entries through a function. -/
theorem mv_bigSepM_fmap {V V' : Type} (Φ : Loc → V' → IProp GF) (f : V → V') (m : GMap Loc V) :
    ([∗map] k ↦ y ∈ GMap.fmap f m, Φ k y) ⊣⊢ [∗map] k ↦ x ∈ m, Φ k (f x) := by
  refine Iris.Std.LawfulFiniteMap.induction_on (M := GMap Loc) (K := Loc)
    (P := fun m => ([∗map] k ↦ y ∈ GMap.fmap f m, Φ k y) ⊣⊢ [∗map] k ↦ x ∈ m, Φ k (f x)) ?_ ?_ m
  · show ([∗map] k ↦ y ∈ GMap.fmap f (∅ : GMap Loc V), Φ k y) ⊣⊢ [∗map] k ↦ x ∈ (∅ : GMap Loc V), Φ k (f x)
    rw [GMap.fmap_empty]
    exact ⟨BigSepM.bigSepM_empty.1.trans BigSepM.bigSepM_empty.2, BigSepM.bigSepM_empty.1.trans BigSepM.bigSepM_empty.2⟩
  · intro k x m hk ih
    show ([∗map] k' ↦ y ∈ GMap.fmap f (<[k := x]> m), Φ k' y) ⊣⊢ [∗map] k' ↦ x' ∈ <[k := x]> m, Φ k' (f x')
    rw [GMap.fmap_insert]
    have hk' : GMap.fmap f m !! k = none := by
      show (m !! k).map f = none; rw [show m !! k = none from hk]; rfl
    exact (BigSepM.bigSepM_insert hk').trans ((sep_congr .rfl ih).trans (BigSepM.bigSepM_insert (Φ := fun k' x' => Φ k' (f x')) hk).symm)

theorem mv_w64_excl (l : Loc) (v v' : w64) (q : Qp) :
    (typedPointsto l v (DFrac.own 1) : IProp GF) ∗ typedPointsto l v' (DFrac.own q) ⊢ False := by
  iintro ⟨H1, H2⟩
  icases typedPointsto_split _ _ _ $$ H1 with H1
  icases typedPointsto_split _ _ _ $$ H2 with H2
  rw [typedPointstoDef_heap, typedPointstoDef_heap]
  icombine H1 H2 gives % ⟨Hv, -⟩
  exfalso
  rw [DFrac.op_own] at Hv
  have h1 := DFrac.valid_own.1 Hv
  have h2 := q.2
  simp only [Qp.val_add, Qp.val_one] at h1
  grind


/-- Two parts of a watcher's state agree. -/
theorem mv_watcherOwn_agree (w : Loc) (st st' : WatcherSt) (q1 q2 : Qp) :
    watcherOwn (GF := GF) w st q1 ∗ watcherOwn w st' q2 ⊢ ⌜st = st'⌝ := by
  unfold watcherOwn
  iintro ⟨⟨H1, H2, H3, H4, H5⟩, ⟨H1', H2', H3', H4', H5'⟩⟩
  icombine H1 H1' gives %e1
  icombine H2 H2' gives %e2
  icombine H3 H3' gives %e3
  icombine H4 H4' gives %e4
  icombine H5 H5' gives %e5
  ipureintro
  cases st; cases st'; simp_all

/-- The whole state and a part of another: impossible. -/
theorem mv_watcherOwn_excl (w : Loc) (st st' : WatcherSt) (q : Qp) :
    watcherOwn (GF := GF) w st ∗ watcherOwn w st' q ⊢ False := by
  unfold watcherOwn
  iintro ⟨⟨H1, -⟩, ⟨H1', -⟩⟩
  iapply mv_w64_excl $$ [$H1 $H1']

/-- A watcher's state as two halves. -/
theorem mv_watcherOwn_halves (w : Loc) (st : WatcherSt) :
    watcherOwn (GF := GF) w st ⊣⊢ watcherOwn w st (1 : Qp).half ∗ watcherOwn w st (1 : Qp).half := by
  have h := (watcherOwn_fractional (GF := GF) w st).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

/-- The entries of `m` at the keys of `B`, as `B`'s (each entry gives its key's), and the rest. -/
theorem mv_extract {X Y : Type} (Φ : Loc → X → IProp GF) (Ψ : Loc → Y → IProp GF)
    (B : GMap Loc Y) : ∀ (m : GMap Loc X),
    (∀ w y, B !! w = some y → ∃ x, m !! w = some x ∧ (Φ w x ⊢ Ψ w y)) →
    ([∗map] w ↦ x ∈ m, Φ w x) ⊢
      ([∗map] w ↦ y ∈ B, Ψ w y) ∗ [∗map] w ↦ x ∈ GMap.filter (fun w _ => (B !! w).isNone) m, Φ w x := by
  refine Iris.Std.LawfulFiniteMap.induction_on (M := GMap Loc) (K := Loc)
    (P := fun B => ∀ (m : GMap Loc X),
      (∀ w y, B !! w = some y → ∃ x, m !! w = some x ∧ (Φ w x ⊢ Ψ w y)) →
      ([∗map] w ↦ x ∈ m, Φ w x) ⊢
        ([∗map] w ↦ y ∈ B, Ψ w y) ∗ [∗map] w ↦ x ∈ GMap.filter (fun w _ => (B !! w).isNone) m, Φ w x)
    ?_ ?_ B
  · intro m _
    have hf : GMap.filter (fun w _ => ((∅ : GMap Loc Y) !! w).isNone) m = m := by
      apply GMap.ext; intro k
      show (m !! k).filter _ = m !! k
      cases m !! k <;> rfl
    show _ ⊢ ([∗map] w ↦ y ∈ (∅ : GMap Loc Y), Ψ w y) ∗ _
    rw [hf]
    iintro H
    iframe H
    iapply BigSepM.bigSepM_empty.2
    iempintro
  · intro k y B' hk ih m hm
    have hk' : B' !! k = none := hk
    obtain ⟨x, hx, hΦ⟩ := hm k y (GMap.lookup_insert _ _ _)
    have hm' : ∀ w y', B' !! w = some y' → ∃ x', GMap.delete k m !! w = some x' ∧ (Φ w x' ⊢ Ψ w y') := by
      intro w y' hw
      have hne : w ≠ k := by intro e; subst e; rw [hk'] at hw; cases hw
      obtain ⟨x', h1, h2⟩ := hm w y' (by
        change (<[k := y]> B') !! w = some y'
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hw)
      exact ⟨x', by rw [GMap.lookup_delete_ne _ (Ne.symm hne)]; exact h1, h2⟩
    have hf : GMap.filter (fun w _ => ((<[k := y]> B') !! w).isNone) m =
        GMap.filter (fun w _ => (B' !! w).isNone) (GMap.delete k m) := by
      apply GMap.ext; intro w
      show (m !! w).filter (fun _ => ((<[k := y]> B') !! w).isNone) =
        ((GMap.delete k m) !! w).filter (fun _ => (B' !! w).isNone)
      by_cases hw : w = k
      · subst hw; rw [GMap.lookup_delete, GMap.lookup_insert]; cases m !! w <;> rfl
      · rw [GMap.lookup_delete_ne _ (Ne.symm hw), GMap.lookup_insert_ne _ _ (Ne.symm hw)]
    show _ ⊢ ([∗map] w ↦ y ∈ <[k := y]> B', Ψ w y) ∗
      [∗map] w ↦ x ∈ GMap.filter (fun w _ => ((<[k := y]> B') !! w).isNone) m, Φ w x
    rw [hf]
    iintro H
    icases (BigSepM.bigSepM_delete (m := m) hx).1 $$ H with ⟨Hx, H⟩
    rw [mv_std_delete_eq]
    icases ih (GMap.delete k m) hm' $$ H with ⟨HB, Hrest⟩
    iframe Hrest
    iapply (BigSepM.bigSepM_insert (m := B') hk').2
    iframe HB
    iapply hΦ $$ Hx

/-- **Regrouping** the entries of `m` by the disjoint maps of a list (each entry of a map given by
`m`'s at its key; the entries of `m` at no key of the list dropped). -/
theorem mv_regroup {A X Y : Type} (Φ : Loc → X → IProp GF) (Ψ : Loc → Y → IProp GF) :
    ∀ (L : List (A × GMap Loc Y)) (m : GMap Loc X),
    (∀ (i j : Nat) (x x' : A × GMap Loc Y) (w : Loc), L[i]? = some x → L[j]? = some x' →
      (x.2 !! w).isSome → (x'.2 !! w).isSome → i = j) →
    (∀ (i : Nat) (x : A × GMap Loc Y) (w : Loc) (y : Y), L[i]? = some x → x.2 !! w = some y →
      ∃ v, m !! w = some v ∧ (Φ w v ⊢ Ψ w y)) →
    ([∗map] w ↦ v ∈ m, Φ w v) ⊢ [∗list] x ∈ L, [∗map] w ↦ y ∈ x.2, Ψ w y
  | [], m, _, _ => by
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | a :: L, m, hd, hc => by
    iintro H
    icases mv_extract Φ Ψ a.2 m (fun w y h => hc 0 a w y rfl h) $$ H with ⟨Ha, H⟩
    iapply BigSepL.bigSepL_cons.2
    iframe Ha
    iapply mv_regroup Φ Ψ L _ (fun i j x x' w h1 h2 h3 h4 => by
        have := hd (i + 1) (j + 1) x x' w h1 h2 h3 h4; omega)
      (fun i x w y hi hy => by
        obtain ⟨v, h1, h2⟩ := hc (i + 1) x w y hi hy
        refine ⟨v, ?_, h2⟩
        show (m !! w).filter _ = some v
        have hn : (a.2 !! w).isNone = true := by
          cases ha : a.2 !! w with
          | none => rfl
          | some _ => have := hd 0 (i + 1) a x w rfl hi (by rw [ha]; rfl) (by rw [hy]; rfl); omega
        rw [h1]; simp [hn]) $$ H

end generic

/-! ## The lock's state transitions (pure) -/

/-- The victims' states. -/
abbrev vicSt (σ : WsState) : GMap Loc WatcherSt :=
  GMap.filter (fun w _ => (σ.victimOf w).isSome) σ.ST

/-- The lock's state once the mover took the victims out (the victims slice now `vs`, empty):
the victims' states out (`Wo`), their delivered events dropped. -/
def takeState (σ : WsState) (vs : GoSlice) : WsState :=
  { σ with ST := GMap.filter (fun w _ => !(σ.victimOf w).isSome) σ.ST,
           Wo := σ.Wo ∪ vicSt σ,
           E := GMap.filter (fun w _ => !(σ.victimOf w).isSome) σ.E,
           vs := vs, vbs := [], VB := [] }

theorem takeState_victimOf (σ : WsState) (vs : GoSlice) (w : Loc) :
    (takeState σ vs).victimOf w = none := rfl

theorem WsOk.not_vic_of_ws {σ : WsState} (h : WsOk σ) {w : Loc} (hw : (σ.Ws !! w).isSome) :
    (σ.victimOf w).isSome = false := by rw [h.ws_v w hw]; rfl

theorem WsOk.not_vic_of_wu {σ : WsState} (h : WsOk σ) {w : Loc} (hw : (σ.Wu !! w).isSome) :
    (σ.victimOf w).isSome = false := by rw [h.wu_v w hw]; rfl

theorem takeState_live (σ : WsState) (vs : GoSlice) (w : Loc) :
    (takeState σ vs).live w ↔ ((σ.Ws !! w).isSome ∨ (σ.Wu !! w).isSome) := by
  unfold WsState.live; rw [takeState_victimOf]; simp [takeState]

theorem takeState_ok {σ : WsState} (h : WsOk σ) (vs : GoSlice) : WsOk (takeState σ vs) := by
  have hlv := takeState_live σ vs
  have hlive_of : ∀ w, (takeState σ vs).live w → σ.live w ∧ (σ.victimOf w).isSome = false := by
    intro w hw
    rcases (hlv w).1 hw with hw | hw
    · exact ⟨Or.inl hw, h.not_vic_of_ws hw⟩
    · exact ⟨Or.inr (Or.inl hw), h.not_vic_of_wu hw⟩
  have hlive_to : ∀ w, σ.live w → (σ.victimOf w).isSome = false → (takeState σ vs).live w := by
    intro w hw hv
    rw [hlv]
    rcases hw with hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr hw
    · rw [hv] at hw; cases hw
  have hST : ∀ w, (takeState σ vs).ST !! w = (σ.ST !! w).filter (fun _ => !(σ.victimOf w).isSome) :=
    fun w => rfl
  have hE : ∀ w, (takeState σ vs).E !! w = (σ.E !! w).filter (fun _ => !(σ.victimOf w).isSome) :=
    fun w => rfl
  have hWo : ∀ w, (takeState σ vs).Wo !! w =
      (σ.Wo !! w).or ((σ.ST !! w).filter (fun _ => (σ.victimOf w).isSome)) := fun w => rfl
  constructor
  · exact h.ws_wu
  · intro w _; rfl
  · intro w _; rfl
  · intro i j B B' w hi; simp [takeState] at hi
  · intro w hw
    obtain ⟨hl, hv⟩ := hlive_of w hw
    rw [hST, hv]
    have := h.live_st w hl
    cases hs : σ.ST !! w <;> simp_all
  · intro w
    rw [hE]
    constructor
    · intro he
      cases hv : (σ.victimOf w).isSome
      · rw [hv] at he
        apply hlive_to w _ hv
        exact (h.live_e w).1 (by cases h' : σ.E !! w <;> simp_all)
      · rw [hv] at he; cases h' : σ.E !! w <;> simp_all
    · intro hw
      obtain ⟨hl, hv⟩ := hlive_of w hw
      rw [hv]
      have := (h.live_e w).2 hl
      cases h' : σ.E !! w <;> simp_all
  · intro w hw
    rw [hST] at hw
    apply h.st_m w
    cases hs : σ.ST !! w <;> simp_all
  · intro w hw
    rw [hWo] at hw
    cases ho : σ.Wo !! w with
    | some _ => exact h.wo_m w (by rw [ho]; rfl)
    | none =>
      rw [ho] at hw
      apply h.st_m w
      cases hs : σ.ST !! w <;> simp_all
  · intro w hm
    rcases h.m_st w hm with hs | hs
    · cases hv : (σ.victimOf w).isSome
      · left; rw [hST, hv]; cases h' : σ.ST !! w <;> simp_all
      · right; rw [hWo]
        cases h' : σ.Wo !! w <;> cases h'' : σ.ST !! w <;> simp_all
    · right; rw [hWo]; cases h' : σ.Wo !! w <;> simp_all
  · intro w hw
    rw [hWo] at hw
    rw [hST]
    cases ho : σ.Wo !! w with
    | some _ => rw [h.wo_st w (by rw [ho]; rfl)]; rfl
    | none =>
      rw [ho] at hw
      cases hs : σ.ST !! w <;> cases hv : (σ.victimOf w).isSome <;> simp_all
  · intro w hw hl
    obtain ⟨hl, hv⟩ := hlive_of w hl
    rw [hWo] at hw
    cases ho : σ.Wo !! w with
    | some _ => exact h.wo_live w (by rw [ho]; rfl) hl
    | none => rw [ho] at hw; cases hs : σ.ST !! w <;> simp_all
  · intro w st hw
    rw [hST] at hw
    cases hv : (σ.victimOf w).isSome
    · rw [hv] at hw
      have hs : σ.ST !! w = some st := by cases h' : σ.ST !! w <;> simp_all
      obtain ⟨h1, h2, h3, h4⟩ := h.st_flags w st hs
      refine ⟨h1, h2, fun hl => ?_, ?_⟩
      · rw [takeState_victimOf]
        obtain ⟨hl', -⟩ := hlive_of w hl
        rw [h3 hl', hv]; simp
      · rw [h4]
        constructor
        · intro hn hl; exact hn (hlive_of w hl).1
        · intro hn hl; exact hn (hlive_to w hl hv)
    · rw [hv] at hw; cases h' : σ.ST !! w <;> simp_all
  · intro w st hw
    rw [hWo] at hw
    cases ho : σ.Wo !! w with
    | some st0 => rw [ho] at hw; simp only [Option.some_or, Option.some.injEq] at hw; subst hw; exact h.wo_flags w _ ho
    | none =>
      rw [ho] at hw
      cases hs : σ.ST !! w with
      | none => simp_all
      | some st0 =>
        rw [hs] at hw
        cases hv : (σ.victimOf w).isSome
        · simp_all
        · simp only [hv] at hw
          simp only [Option.none_or, Option.filter_some, ↓reduceIte, Option.some.injEq] at hw
          subst hw
          obtain ⟨h1, h2, h3, h4⟩ := h.st_flags w _ hs
          have hl : σ.live w := Or.inr (Or.inr hv)
          refine ⟨h1, h2, (h3 hl).2 hv, fun e => ?_⟩
          exact (h4.1 e) hl
  · intro w γw ed hw hm he
    rw [hE] at he
    have := h.synced_d w γw ed hw hm (by cases h' : σ.E !! w <;> simp_all)
    exact this

/-- The lock's state with the watcher `w`, out with the mover, back (synced if `b`, else
unsynced) with its state `st` and delivered events `e`. -/
def readdState (σ : WsState) (w : Loc) (r : WatchRange) (st : WatcherSt) (b : Bool)
    (e : List EvM × Nat) : WsState :=
  { σ with Ws := if b then <[w := r]> σ.Ws else σ.Ws,
           Wu := if b then σ.Wu else <[w := r]> σ.Wu,
           ST := <[w := st]> σ.ST, Wo := GMap.delete w σ.Wo, E := <[w := e]> σ.E }

theorem readdState_victimOf (σ : WsState) (w : Loc) (r : WatchRange) (st : WatcherSt) (b : Bool)
    (e : List EvM × Nat) (w' : Loc) : (readdState σ w r st b e).victimOf w' = σ.victimOf w' := rfl

/-- What a watcher out with the mover is not. -/
theorem WsOk.out {σ : WsState} (h : WsOk σ) {w : Loc} {st : WatcherSt} (hw : σ.Wo !! w = some st) :
    σ.ST !! w = none ∧ ¬ σ.live w ∧ σ.Ws !! w = none ∧ σ.Wu !! w = none ∧ σ.victimOf w = none ∧
      σ.E !! w = none := by
  have hl := h.wo_live w (by rw [hw]; rfl)
  refine ⟨h.wo_st w (by rw [hw]; rfl), hl, ?_, ?_, ?_, ?_⟩
  · cases h' : σ.Ws !! w with
    | none => rfl
    | some _ => exact absurd (Or.inl (by rw [h']; rfl)) hl
  · cases h' : σ.Wu !! w with
    | none => rfl
    | some _ => exact absurd (Or.inr (Or.inl (by rw [h']; rfl))) hl
  · cases h' : σ.victimOf w with
    | none => rfl
    | some _ => exact absurd (Or.inr (Or.inr (by rw [h']; rfl))) hl
  · cases h' : σ.E !! w with
    | none => rfl
    | some _ => exact absurd ((h.live_e w).1 (by rw [h']; rfl)) hl

theorem readdState_live (σ : WsState) (w : Loc) (r : WatchRange) (st : WatcherSt) (b : Bool)
    (e : List EvM × Nat) (w' : Loc) :
    (readdState σ w r st b e).live w' ↔ (w' = w ∨ σ.live w') := by
  unfold WsState.live
  rw [readdState_victimOf]
  by_cases hw : w' = w
  · subst hw; cases b <;> simp [readdState, GMap.lookup_insert]
  · have hw' : ¬ w = w' := fun e => hw e.symm
    cases b <;> simp [readdState, hw, hw']

theorem readdState_ok {σ : WsState} (h : WsOk σ) {w : Loc} {st0 : WatcherSt} (r : WatchRange)
    (hw : σ.Wo !! w = some st0) (b : Bool) (e : List EvM × Nat)
    (hd : b = true → ∀ γw, σ.M !! w = some γw → max γw.lo σ.Lmu.length ≤ e.2) :
    WsOk (readdState σ w r { st0 with victim := false } b e) := by
  obtain ⟨hST, hl, hWs, hWu, hv, hE⟩ := h.out hw
  obtain ⟨hc, hr, -, hch⟩ := h.wo_flags w st0 hw
  have hlv := readdState_live σ w r { st0 with victim := false } b e
  have hvo := readdState_victimOf σ w r { st0 with victim := false } b e
  constructor
  · intro w' h1
    by_cases hx : w' = w
    · subst hx; cases b <;> simp_all [readdState]
    · have hx' : ¬ w = w' := fun e => hx e.symm
      cases b <;> simp_all [readdState] <;> exact h.ws_wu w' h1
  · intro w' h1
    rw [hvo]
    by_cases hx : w' = w
    · subst hx; exact hv
    · have hx' : ¬ w = w' := fun e => hx e.symm
      cases b <;> simp_all [readdState] <;> exact h.ws_v w' h1
  · intro w' h1
    rw [hvo]
    by_cases hx : w' = w
    · subst hx; exact hv
    · have hx' : ¬ w = w' := fun e => hx e.symm
      cases b <;> simp_all [readdState] <;> exact h.wu_v w' h1
  · exact h.v_one
  · intro w' h1
    by_cases hx : w' = w
    · subst hx; simp [readdState, GMap.lookup_insert]
    · show (<[w := _]> σ.ST !! w').isSome
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)]
      exact h.live_st w' (((hlv w').1 h1).resolve_left hx)
  · intro w'
    rw [hlv]
    by_cases hx : w' = w
    · subst hx; simp [readdState, GMap.lookup_insert]
    · show (<[w := e]> σ.E !! w').isSome ↔ _
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), h.live_e]; simp [hx]
  · intro w' h1
    by_cases hx : w' = w
    · subst hx; exact h.wo_m w' (by rw [hw]; rfl)
    · have : (σ.ST !! w').isSome := by
        have h1' : (<[w := _]> σ.ST !! w').isSome := h1
        rwa [GMap.lookup_insert_ne _ _ (Ne.symm hx)] at h1'
      exact h.st_m w' this
  · intro w' h1
    by_cases hx : w' = w
    · subst hx; exact h.wo_m w' (by rw [hw]; rfl)
    · have h1' : (GMap.delete w σ.Wo !! w').isSome := h1
      rw [GMap.lookup_delete_ne _ (Ne.symm hx)] at h1'
      exact h.wo_m w' h1'
  · intro w' h1
    by_cases hx : w' = w
    · subst hx; left; simp [readdState, GMap.lookup_insert]
    · rcases h.m_st w' h1 with h2 | h2
      · left; show (<[w := _]> σ.ST !! w').isSome; rwa [GMap.lookup_insert_ne _ _ (Ne.symm hx)]
      · right; show (GMap.delete w σ.Wo !! w').isSome; rwa [GMap.lookup_delete_ne _ (Ne.symm hx)]
  · intro w' h1
    by_cases hx : w' = w
    · subst hx; simp [readdState, GMap.lookup_delete] at h1
    · have h1' : (GMap.delete w σ.Wo !! w').isSome := h1
      rw [GMap.lookup_delete_ne _ (Ne.symm hx)] at h1'
      show <[w := _]> σ.ST !! w' = none
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)]; exact h.wo_st w' h1'
  · intro w' h1 hl'
    by_cases hx : w' = w
    · subst hx; simp [readdState, GMap.lookup_delete] at h1
    · have h1' : (GMap.delete w σ.Wo !! w').isSome := h1
      rw [GMap.lookup_delete_ne _ (Ne.symm hx)] at h1'
      exact h.wo_live w' h1' (((hlv w').1 hl').resolve_left hx)
  · intro w' st' h1
    by_cases hx : w' = w
    · subst hx
      have h1' : <[w' := { st0 with victim := false }]> σ.ST !! w' = some st' := h1
      rw [GMap.lookup_insert] at h1'; cases h1'
      refine ⟨hc, hr, fun _ => ?_, ?_⟩
      · rw [hvo, hv]; simp
      · constructor
        · intro e'; exact absurd e' hch
        · intro hn; exact absurd ((hlv w').2 (Or.inl rfl)) hn
    · have h1' : <[w := { st0 with victim := false }]> σ.ST !! w' = some st' := h1
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)] at h1'
      obtain ⟨h1, h2, h3, h4⟩ := h.st_flags w' st' h1'
      refine ⟨h1, h2, fun hl' => ?_, ?_⟩
      · rw [hvo]; exact h3 (((hlv w').1 hl').resolve_left hx)
      · rw [h4, hlv]; simp [hx]
  · intro w' st' h1
    by_cases hx : w' = w
    · subst hx; simp [readdState, GMap.lookup_delete] at h1
    · have h1' : GMap.delete w σ.Wo !! w' = some st' := h1
      rw [GMap.lookup_delete_ne _ (Ne.symm hx)] at h1'
      exact h.wo_flags w' st' h1'
  · intro w' γw ed h1 hm he
    by_cases hx : w' = w
    · subst hx
      have he' : <[w' := e]> σ.E !! w' = some ed := he
      rw [GMap.lookup_insert] at he'; cases he'
      cases b
      · simp [readdState, hWs] at h1
      · exact hd rfl γw hm
    · have h1' : ((if b then <[w := r]> σ.Ws else σ.Ws) !! w').isSome := h1
      have he' : <[w := e]> σ.E !! w' = some ed := he
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)] at he'
      cases b
      · exact h.synced_d w' γw ed h1' hm he'
      · simp only [↓reduceIte] at h1'
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)] at h1'
        exact h.synced_d w' γw ed h1' hm he'

/-- A watcher whose batch the mover failed to send: the batch's pointer and model, the watcher's
state and delivered events. -/
structure NvEnt where
  eb : Loc
  B : EventBatch
  st : WatcherSt
  evsw : List EvM
  γw : WatcherNames

/-- The lock's state with the failed watchers `NV` (out with the mover) back as victims, in one
batch map `nvm` appended to the victims slice (now `vs`). -/
def appendState (σ : WsState) (NV : GMap Loc NvEnt) (vs : GoSlice) (nvm : GoMap) : WsState :=
  { σ with ST := σ.ST ∪ GMap.fmap NvEnt.st NV,
           Wo := GMap.filter (fun w _ => (NV !! w).isNone) σ.Wo,
           E := σ.E ∪ GMap.fmap (fun x => (x.evsw, sint.nat x.st.minRev)) NV,
           vs := vs, vbs := σ.vbs ++ [nvm], VB := σ.VB ++ [GMap.fmap NvEnt.B NV] }

theorem appendState_victimOf (σ : WsState) (NV : GMap Loc NvEnt) (vs : GoSlice) (nvm : GoMap)
    (w : Loc) :
    (appendState σ NV vs nvm).victimOf w = (σ.victimOf w).or ((NV !! w).map NvEnt.B) := by
  unfold WsState.victimOf appendState
  simp only
  rw [List.findSome?_append]; simp

theorem appendState_ok {σ : WsState} (h : WsOk σ) (NV : GMap Loc NvEnt) (vs : GoSlice)
    (nvm : GoMap) (hNV : ∀ w x, NV !! w = some x → σ.Wo !! w = some x.st) :
    WsOk (appendState σ NV vs nvm) := by
  have hvo := appendState_victimOf σ NV vs nvm
  have hout : ∀ w, (NV !! w).isSome → σ.ST !! w = none ∧ ¬ σ.live w ∧ σ.Ws !! w = none ∧
      σ.Wu !! w = none ∧ σ.victimOf w = none ∧ σ.E !! w = none := by
    intro w hw
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hw
    exact h.out (hNV w x hx)
  have hlv : ∀ w, (appendState σ NV vs nvm).live w ↔ (σ.live w ∨ (NV !! w).isSome) := by
    intro w
    unfold WsState.live
    rw [hvo]
    show (σ.Ws !! w).isSome = true ∨ (σ.Wu !! w).isSome = true ∨
      ((σ.victimOf w).or ((NV !! w).map NvEnt.B)).isSome = true ↔ _
    cases hn : NV !! w <;> cases hv : σ.victimOf w <;> simp
  have hnn : ∀ w, (NV !! w).isSome = false → (appendState σ NV vs nvm).victimOf w = σ.victimOf w := by
    intro w hn; rw [hvo]; cases h' : NV !! w <;> simp_all
  have hST : ∀ w, (appendState σ NV vs nvm).ST !! w = (σ.ST !! w).or ((NV !! w).map NvEnt.st) :=
    fun w => rfl
  have hE : ∀ w, (appendState σ NV vs nvm).E !! w =
      (σ.E !! w).or ((NV !! w).map (fun x => (x.evsw, sint.nat x.st.minRev))) := fun w => rfl
  have hWo : ∀ w, (appendState σ NV vs nvm).Wo !! w = (σ.Wo !! w).filter (fun _ => (NV !! w).isNone) :=
    fun w => rfl
  constructor
  · exact h.ws_wu
  · intro w h1
    have hn : (NV !! w).isSome = false := by
      cases hn : NV !! w with
      | none => rfl
      | some _ =>
        have := (hout w (by rw [hn]; rfl)).2.2.1
        have h1' : (σ.Ws !! w).isSome = true := h1
        rw [this] at h1'; cases h1'
    rw [hnn w hn]; exact h.ws_v w h1
  · intro w h1
    have hn : (NV !! w).isSome = false := by
      cases hn : NV !! w with
      | none => rfl
      | some _ =>
        have := (hout w (by rw [hn]; rfl)).2.2.2.1
        have h1' : (σ.Wu !! w).isSome = true := h1
        rw [this] at h1'; cases h1'
    rw [hnn w hn]; exact h.wu_v w h1
  · intro i j B B' w hi hj hB hB'
    show i = j
    unfold appendState at hi hj
    simp only at hi hj
    by_cases hi' : i < σ.VB.length <;> by_cases hj' : j < σ.VB.length
    · rw [List.getElem?_append_left hi'] at hi
      rw [List.getElem?_append_left hj'] at hj
      exact h.v_one i j B B' w hi hj hB hB'
    · exfalso
      rw [List.getElem?_append_left hi'] at hi
      rw [List.getElem?_append_right (by omega)] at hj
      have hj1 : j - σ.VB.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 hj).1; simp at this; omega
      rw [hj1] at hj; simp at hj; subst hj
      have hw : (NV !! w).isSome := by simpa using hB'
      have := (hout w hw).2.2.2.2.1
      unfold WsState.victimOf at this
      rw [List.findSome?_eq_none_iff] at this
      have := this B (List.mem_of_getElem? hi)
      rw [this] at hB; cases hB
    · exfalso
      rw [List.getElem?_append_left hj'] at hj
      rw [List.getElem?_append_right (by omega)] at hi
      have hi1 : i - σ.VB.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
      rw [hi1] at hi; simp at hi; subst hi
      have hw : (NV !! w).isSome := by simpa using hB
      have := (hout w hw).2.2.2.2.1
      unfold WsState.victimOf at this
      rw [List.findSome?_eq_none_iff] at this
      have := this B' (List.mem_of_getElem? hj)
      rw [this] at hB'; cases hB'
    · have h1 := (List.getElem?_eq_some_iff.1 hi).1
      have h2 := (List.getElem?_eq_some_iff.1 hj).1
      simp at h1 h2; omega
  · intro w h1
    rw [hlv] at h1
    rw [hST]
    rcases h1 with h1 | h1
    · have := h.live_st w h1; cases h' : σ.ST !! w <;> simp_all
    · cases h' : σ.ST !! w <;> cases h'' : NV !! w <;> simp_all
  · intro w
    rw [hE, hlv]
    cases hn : NV !! w with
    | none => simp [h.live_e w]
    | some x =>
      have := (hout w (by rw [hn]; rfl)).2.2.2.2.2
      simp [this]
  · intro w h1
    rw [hST] at h1
    cases hs : σ.ST !! w with
    | some _ => exact h.st_m w (by rw [hs]; rfl)
    | none =>
      rw [hs] at h1
      cases hn : NV !! w with
      | none => rw [hn] at h1; cases h1
      | some x => exact h.wo_m w (by rw [hNV w x hn]; rfl)
  · intro w h1
    rw [hWo] at h1
    exact h.wo_m w (by cases h' : σ.Wo !! w <;> simp_all)
  · intro w hm
    rcases h.m_st w hm with h1 | h1
    · left; rw [hST]; cases h' : σ.ST !! w <;> simp_all
    · cases hn : NV !! w with
      | none => right; rw [hWo]; cases h' : σ.Wo !! w <;> simp_all
      | some x => left; rw [hST]; cases h' : σ.ST !! w <;> simp_all
  · intro w h1
    rw [hWo] at h1
    rw [hST]
    have ho : (σ.Wo !! w).isSome := by cases h' : σ.Wo !! w <;> simp_all
    have hn : NV !! w = none := by
      cases h' : NV !! w with
      | none => rfl
      | some _ => cases h'' : σ.Wo !! w <;> simp_all
    rw [h.wo_st w ho, hn]; rfl
  · intro w h1 hl
    rw [hWo] at h1
    have ho : (σ.Wo !! w).isSome := by cases h' : σ.Wo !! w <;> simp_all
    have hn : NV !! w = none := by
      cases h' : NV !! w with
      | none => rfl
      | some _ => cases h'' : σ.Wo !! w <;> simp_all
    rw [hlv, hn] at hl
    rcases hl with hl | hl
    · exact h.wo_live w ho hl
    · cases hl
  · intro w st h1
    rw [hST] at h1
    cases hs : σ.ST !! w with
    | some st0 =>
      rw [hs] at h1; simp only [Option.some_or, Option.some.injEq] at h1; subst h1
      have hn : NV !! w = none := by
        cases h' : NV !! w with
        | none => rfl
        | some _ => have := (hout w (by rw [h']; rfl)).1; rw [hs] at this; cases this
      obtain ⟨h1, h2, h3, h4⟩ := h.st_flags w _ hs
      refine ⟨h1, h2, fun hl => ?_, ?_⟩
      · rw [hnn w (by rw [hn]; rfl)]
        exact h3 (by rw [hlv, hn] at hl; simpa using hl)
      · rw [h4, hlv, hn]; simp
    | none =>
      rw [hs] at h1
      cases hn : NV !! w with
      | none => rw [hn] at h1; cases h1
      | some x =>
        rw [hn] at h1; simp only [Option.none_or, Option.map_some, Option.some.injEq] at h1
        subst h1
        obtain ⟨h1, h2, h3, h4⟩ := h.wo_flags w _ (hNV w x hn)
        refine ⟨h1, h2, fun _ => ?_, ?_⟩
        · rw [hvo, hn, h3]; simp
        · constructor
          · intro e; exact absurd e h4
          · intro hl; exact absurd ((hlv w).2 (Or.inr (by rw [hn]; rfl))) hl
  · intro w st h1
    rw [hWo] at h1
    exact h.wo_flags w st (by cases h' : σ.Wo !! w <;> simp_all)
  · intro w γw ed h1 hm he
    rw [hE] at he
    have hn : NV !! w = none := by
      cases h' : NV !! w with
      | none => rfl
      | some _ =>
        have := (hout w (by rw [h']; rfl)).2.2.1
        have h1' : (σ.Ws !! w).isSome = true := h1
        rw [this] at h1'; cases h1'
    rw [hn] at he
    exact h.synced_d w γw ed h1 hm (by cases h' : σ.E !! w <;> simp_all)

/-- The batch of a victim is the one batch it is in. -/
theorem mv_findSome_unique {Y : Type} (w : Loc) (y : Y) :
    ∀ (L : List (GMap Loc Y)) (i : Nat) (B : GMap Loc Y), L[i]? = some B → B !! w = some y →
    (∀ j B', L[j]? = some B' → (B' !! w).isSome → j = i) → L.findSome? (· !! w) = some y
  | [], i, B, h, _, _ => by simp at h
  | x :: L, 0, B, h, hB, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [List.findSome?_cons, hB]
  | x :: L, i + 1, B, h, hB, hu => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.findSome?_cons]
    cases hx : x !! w with
    | some _ => have := hu 0 x rfl (by rw [hx]; rfl); omega
    | none =>
      exact mv_findSome_unique w y L i B h hB (fun j B' hj hw => by
        have := hu (j + 1) B' hj hw; omega)

theorem WsOk.victimOf_of_mem {σ : WsState} (h : WsOk σ) {i : Nat} {B : GMap Loc EventBatch}
    {w : Loc} {y : EventBatch} (hi : σ.VB[i]? = some B) (hw : B !! w = some y) :
    σ.victimOf w = some y :=
  mv_findSome_unique w y σ.VB i B hi hw (fun j B' hj hw' =>
    h.v_one j i B' B w hj hi hw' (by rw [hw]; rfl))

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A victim out with the mover with its batch `B` (its state as the mover took it). -/
def outW (γ : WsNames) (w : Loc) (B : EventBatch) : IProp GF := iprop(∃ st, moverRes γ w st B)

/-- `moverRes` with its delivered events and names explicit. -/
def moverResG (γ : WsNames) (w : Loc) (st : WatcherSt) (B : EventBatch) (evsw : List EvM)
    (γw : WatcherNames) : IProp GF :=
  iprop(∃ (r : WatchRange) (fcs : GoSlice),
    watcherMeta γ w γw ∗ watcherFixed w r fcs ∗ watcherChan γ w γw st.ch ∗ filtersOk fcs ∗
    ⌜sint.Z r.startRev ≤ (γw.lo : Int) ∧ (γw.lo : Int) ≤ sint.Z st.minRev ∧
      victimBatchOk γw.lo st B⌝ ∗
    watcherOwn w st (1 : Qp).half ∗ monoListAuthOwn γw.evs (1 : Qp).half evsw ∗
    dghostVar γw.live (DFrac.own (1 : Qp).half) true ∗
    evsWf γ r γw.lo (evsw ++ B.evs) (sint.nat st.minRev))

theorem moverRes_G (γ : WsNames) (w : Loc) (st : WatcherSt) (B : EventBatch) :
    moverRes (GF := GF) γ w st B ⊣⊢ ∃ evsw γw, moverResG γ w st B evsw γw := by
  unfold moverRes moverResG
  constructor
  · iintro ⟨%γw, %r, %fcs, %evsw, H⟩; iexists evsw, γw, r, fcs; iexact H
  · iintro ⟨%evsw, %γw, %r, %fcs, H⟩; iexists γw, r, fcs, evsw; iexact H

theorem mv_memberRes_congr (γ : WsNames) (q : Qp) (σ σ' : WsState) (w : Loc) (st : WatcherSt)
    (hM : σ'.M = σ.M) (hWs : (σ'.Ws !! w).isSome = (σ.Ws !! w).isSome)
    (hWu : (σ'.Wu !! w).isSome = (σ.Wu !! w).isSome) (hV : σ'.victimOf w = σ.victimOf w)
    (hE : σ'.E !! w = σ.E !! w) :
    memberRes (GF := GF) γ q σ w st ⊢ memberRes γ q σ' w st := by
  have hl : σ'.live w = σ.live w := by unfold WsState.live; rw [hWs, hWu, hV]
  unfold memberRes popFacts
  simp only [hM, hl, hWs, hWu, hV, hE]
  exact .rfl

/-- A victim's resources under the lock, out to the mover (its `outRes` stays). -/
theorem mv_member_to_mover (γ : WsNames) (σ : WsState) (hok : WsOk σ) (vs' : GoSlice) (w : Loc)
    (st : WatcherSt) (B : EventBatch) (hB : σ.victimOf w = some B) :
    memberRes (GF := GF) γ 1 σ w st ∗ watcherOwn w st (1 : Qp).half ⊢
      outRes γ (takeState σ vs') w st ∗ moverRes γ w st B := by
  have hl : σ.live w := Or.inr (Or.inr (by rw [hB]; rfl))
  have hWs : (σ.Ws !! w).isSome = false := by
    cases h : σ.Ws !! w with
    | none => rfl
    | some _ => have := hok.ws_v w (by rw [h]; rfl); rw [hB] at this; cases this
  have hWu : (σ.Wu !! w).isSome = false := by
    cases h : σ.Wu !! w with
    | none => rfl
    | some _ => have := hok.wu_v w (by rw [h]; rfl); rw [hB] at this; cases this
  unfold memberRes popFacts
  simp only [hl, hWs, hWu, hB, ↓reduceIte, Bool.false_eq_true]
  iintro ⟨⟨%γw, %r, %fcs, %hM, #Hm, #Hf, #Hc, #Hfo, %Hsr, %evsw, %d, %hE, Ha, Hl, %Hp, #Hwf⟩, Hown⟩
  obtain ⟨hlo, hd, hvb⟩ := Hp
  subst hd
  isplitr
  · unfold outRes
    iexists γw, r, fcs
    iframe Hm Hf
    ipureintro; exact hM
  unfold moverRes
  iexists γw, r, fcs, evsw
  iframe Hm Hf Hc Hfo Hown Ha Hl Hwf
  ipureintro; exact ⟨Hsr, hlo, hvb⟩

/-- **The victims out**: the lock's body at the state with the victims taken out (the victims
slice now the nil slice `vnil`), and the mover's per batch (`vbs.zip VB`) victims. -/
theorem body_take (s : Loc) (γ : WsNames) (σ : WsState) (hok : WsOk σ) (vnil : GoSlice) :
    ghostVar (GF := GF) γ.wst 1 (takeState σ vnil) ∗ ghostVar γ.wlog (1 : Qp).half σ.Lmu ∗
      idxCert γ.st.idx σ.Lmu ∗
      ownWatcherGroup (syncedAddr s) σ.Ws ∗ ownWatcherGroup (unsyncedAddr s) σ.Wu ∗
      typedPointsto (victimsAddr s) vnil (DFrac.own 1) ∗ ownSlice vnil ([] : List GoMap) (DFrac.own 1) ∗
      ownSliceCap GoMap vnil (DFrac.own 1) ∗
      ([∗map] w ↦ st ∈ σ.ST, watcherOwn w st) ∗
      ([∗map] w ↦ st ∈ σ.Wo, watcherOwn w st (1 : Qp).half) ∗ ghostMapAuth γ.wmeta 1 σ.M ∗
      ([∗map] w ↦ _γw ∈ σ.M, ∃ (r : WatchRange) (fcs : GoSlice), watcherFixed w r fcs) ∗
      ([∗map] w ↦ st ∈ σ.ST, memberRes γ 1 σ w st) ∗
      ([∗map] w ↦ st ∈ σ.Wo, outRes γ σ w st) ⊢
    watchStoreBody s γ 1 (takeState σ vnil) ∗
      [∗list] x ∈ σ.vbs.zip σ.VB, [∗map] w ↦ b ∈ x.2, outW γ w b := by
  iintro ⟨Hσ, Hwlog, #Hcert, Hsy, Hun, Hvf, Hvs, Hvcap, Hst, Hwo, Hmeta, #Hmfix, Hmem, #Hout⟩
  let p : Loc → WatcherSt → Bool := fun w _ => (σ.victimOf w).isSome
  icases (mv_bigSepM_split _ p σ.ST).1 $$ Hst with ⟨HstV, HstN⟩
  icases (mv_bigSepM_split _ p σ.ST).1 $$ Hmem with ⟨HmV, HmN⟩
  ihave HstV2 : ([∗map] w ↦ st ∈ vicSt σ, watcherOwn w st (1 : Qp).half) ∗
      ([∗map] w ↦ st ∈ vicSt σ, watcherOwn w st (1 : Qp).half) $$ [HstV]
  · iapply (mv_bigSepM_sep _ _ _).1
    iapply (BigSepM.bigSepM_mono (fun {k v} _ => (mv_watcherOwn_halves k v).1)) $$ HstV
  icases HstV2 with ⟨HstVa, HstVb⟩
  ihave HV : [∗map] w ↦ st ∈ vicSt σ, outRes γ (takeState σ vnil) w st ∗
      moverRes γ w st ((σ.victimOf w).getD EventBatch.empty) $$ [HmV HstVb]
  · ihave H := (mv_bigSepM_sep _ _ _).2 $$ [HmV HstVb]
    · iframe HmV HstVb
    iapply (BigSepM.bigSepM_mono (fun {k v} hk => ?_)) $$ H
    have hk' : (σ.victimOf k).isSome := by
      have : (vicSt σ) !! k = some v := hk
      unfold vicSt at this; rw [GMap.lookup_filter] at this
      cases h : σ.victimOf k <;> cases h' : σ.ST !! k <;> simp_all
    obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hk'
    rw [hB]
    exact mv_member_to_mover γ σ hok vnil k v B hB
  icases (mv_bigSepM_sep _ _ _).1 $$ HV with ⟨#HVo, HVm⟩
  isplitr [HVm]
  · unfold watchStoreBody
    dsimp only [takeState]
    simp only [named]
    iframe Hσ Hwlog Hcert Hsy Hun Hvf Hvs Hvcap Hmeta Hmfix
    isplitr
    · ipureintro; rfl
    isplitr
    · simp only [List.zip_nil_right]
      iapply BigSepL.bigSepL_nil.2; iempintro
    isplitl [HstN]
    · iexact HstN
    isplitl [Hwo HstVa]
    · iapply (mv_bigSepM_union _ σ.Wo (vicSt σ) (fun k hk => by
        unfold vicSt; rw [GMap.lookup_filter, hok.wo_st k hk]; rfl)).2
      iframe Hwo HstVa
    isplitl [HmN]
    · iapply (BigSepM.bigSepM_mono (fun {k v} hk => ?_)) $$ HmN
      have hk' : (σ.victimOf k).isSome = false := by
        have : (GMap.filter (fun k v => !p k v) σ.ST) !! k = some v := hk
        rw [GMap.lookup_filter] at this
        cases h : σ.victimOf k <;> cases h' : σ.ST !! k <;> simp_all [p]
      apply mv_memberRes_congr γ 1 σ (takeState σ vnil) k v rfl rfl rfl
      · rw [takeState_victimOf]; cases h : σ.victimOf k <;> simp_all
      · show (σ.E !! k).filter (fun _ => !(σ.victimOf k).isSome) = σ.E !! k
        rw [hk']; cases σ.E !! k <;> rfl
    isplitr
    · iapply (mv_bigSepM_union _ σ.Wo (vicSt σ) (fun k hk => by
        unfold vicSt; rw [GMap.lookup_filter, hok.wo_st k hk]; rfl)).2
      isplitr
      · iapply (BigSepM.bigSepM_mono (fun {k v} _ => by unfold outRes; exact .rfl)) $$ Hout
      · iexact HVo
    ipureintro; exact takeState_ok hok vnil
  iapply mv_regroup (fun w st => moverRes γ w st ((σ.victimOf w).getD EventBatch.empty))
    (fun w b => outW γ w b) (σ.vbs.zip σ.VB) (vicSt σ) ?_ ?_ $$ HVm
  · intro i j x x' w hi hj hw hw'
    rw [List.getElem?_zip_eq_some] at hi hj
    exact hok.v_one i j x.2 x'.2 w hi.2 hj.2 hw hw'
  · intro i x w y hi hy
    rw [List.getElem?_zip_eq_some] at hi
    have hv := hok.victimOf_of_mem hi.2 hy
    obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 (hok.live_st w (Or.inr (Or.inr (by rw [hv]; rfl))))
    refine ⟨st, ?_, ?_⟩
    · unfold vicSt; rw [GMap.lookup_filter, hst, hv]; rfl
    · rw [hv]; simp only [Option.getD_some]; unfold outW; iintro H; iexists st; iexact H

/-- **The mover's watcher is out** in the lock's state: its names give it a state under the lock
or out, and its half of the state excludes the first and agrees with the second. -/
theorem mv_wo_lookup (γ : WsNames) (σ : WsState) (hok : WsOk σ) (w : Loc) (γw : WatcherNames)
    (st : WatcherSt) :
    ghostMapAuth (GF := GF) γ.wmeta 1 σ.M ∗ watcherMeta γ w γw ∗
      ([∗map] k ↦ v ∈ σ.ST, watcherOwn k v) ∗ ([∗map] k ↦ v ∈ σ.Wo, watcherOwn k v (1 : Qp).half) ∗
      watcherOwn w st (1 : Qp).half ⊢ ⌜σ.Wo !! w = some st⌝ := by
  iintro ⟨Hmeta, #Hm, Hst, Hwo, Hw⟩
  unfold watcherMeta
  ihave %HM := ghost_map_lookup $$ Hmeta Hm
  rcases hok.m_st w (by rw [show σ.M !! w = some γw from HM]; rfl) with h | h
  · obtain ⟨st', hst⟩ := Option.isSome_iff_exists.1 h
    icases (BigSepM.bigSepM_lookup_acc (m := σ.ST) hst).1 $$ Hst with ⟨Hw', -⟩
    iexfalso
    iapply mv_watcherOwn_excl $$ [$Hw' $Hw]
  · obtain ⟨st', hst⟩ := Option.isSome_iff_exists.1 h
    icases (BigSepM.bigSepM_lookup_acc (m := σ.Wo) hst).1 $$ Hwo with ⟨Hw', -⟩
    ihave %He := mv_watcherOwn_agree $$ [$Hw' $Hw]
    ipureintro; rw [hst, He]

/-- **A watcher back** from the mover (synced if `b`, else unsynced), its batch sent: the lock's
body at `readdState`. -/
theorem body_readd (s : Loc) (γ : WsNames) (σ σ' : WsState) (hok : WsOk σ) (w : Loc)
    (st : WatcherSt) (hwo : σ.Wo !! w = some st) (r : WatchRange) (b : Bool)
    (γw : WatcherNames) (hM : σ.M !! w = some γw) (fcs : GoSlice) (evsw : List EvM)
    (hlo : (γw.lo : Int) ≤ sint.Z st.minRev) (hsr : sint.Z r.startRev ≤ (γw.lo : Int))
    (hd : b = true → max γw.lo σ.Lmu.length ≤ sint.nat st.minRev)
    (hσ' : σ' = readdState σ w r { st with victim := false } b (evsw, sint.nat st.minRev)) :
    ghostVar (GF := GF) γ.wst 1 σ' ∗
      ghostVar γ.wlog (1 : Qp).half σ.Lmu ∗ idxCert γ.st.idx σ.Lmu ∗
      ownWatcherGroup (syncedAddr s) (if b then <[w := r]> σ.Ws else σ.Ws) ∗
      ownWatcherGroup (unsyncedAddr s) (if b then σ.Wu else <[w := r]> σ.Wu) ∗
      typedPointsto (victimsAddr s) σ.vs (DFrac.own 1) ∗ ownSlice σ.vs σ.vbs (DFrac.own 1) ∗
      ownSliceCap GoMap σ.vs (DFrac.own 1) ∗ ⌜σ.vbs.length = σ.VB.length⌝ ∗
      ([∗list] x ∈ σ.vbs.zip σ.VB, ownWatcherBatch x.1 x.2) ∗
      ([∗map] k ↦ v ∈ σ.ST, watcherOwn k v) ∗ watcherOwn w { st with victim := false } ∗
      ([∗map] k ↦ v ∈ GMap.delete w σ.Wo, watcherOwn k v (1 : Qp).half) ∗
      ghostMapAuth γ.wmeta 1 σ.M ∗
      ([∗map] k ↦ _γw ∈ σ.M, ∃ (r : WatchRange) (fcs : GoSlice), watcherFixed k r fcs) ∗
      ([∗map] k ↦ v ∈ σ.ST, memberRes γ 1 σ k v) ∗ ([∗map] k ↦ v ∈ σ.Wo, outRes γ σ k v) ∗
      watcherMeta γ w γw ∗ watcherFixed w r fcs ∗ watcherChan γ w γw st.ch ∗ filtersOk fcs ∗
      monoListAuthOwn γw.evs (1 : Qp).half evsw ∗ dghostVar γw.live (DFrac.own (1 : Qp).half) true ∗
      evsWf γ r γw.lo evsw (sint.nat st.minRev) ∗
      (if b then iprop(True) else
        ∃ Lc : Log, idxCert γ.st.idx Lc ∗ ⌜sint.Z st.minRev < Lc.length⌝) ⊢
    watchStoreBody s γ 1 σ' := by
  obtain ⟨hST, hl, hWs, hWu, hv, hE⟩ := hok.out hwo
  have hok' : WsOk σ' := hσ' ▸ readdState_ok hok r hwo b (evsw, sint.nat st.minRev)
    (fun hb γw' hm => by rw [hM] at hm; cases hm; exact hd hb)
  have hlv : ∀ k, σ'.live k ↔ (k = w ∨ σ.live k) := by
    rw [hσ']; exact readdState_live σ w r { st with victim := false } b (evsw, sint.nat st.minRev)
  have eL : σ'.Lmu = σ.Lmu := by rw [hσ']; rfl
  have eWs : σ'.Ws = if b then <[w := r]> σ.Ws else σ.Ws := by rw [hσ']; rfl
  have eWu : σ'.Wu = if b then σ.Wu else <[w := r]> σ.Wu := by rw [hσ']; rfl
  have eST : σ'.ST = <[w := { st with victim := false }]> σ.ST := by rw [hσ']; rfl
  have eWo : σ'.Wo = GMap.delete w σ.Wo := by rw [hσ']; rfl
  have eE : σ'.E = <[w := (evsw, sint.nat st.minRev)]> σ.E := by rw [hσ']; rfl
  have eM : σ'.M = σ.M := by rw [hσ']; rfl
  have evs : σ'.vs = σ.vs := by rw [hσ']; rfl
  have evbs : σ'.vbs = σ.vbs := by rw [hσ']; rfl
  have eVB : σ'.VB = σ.VB := by rw [hσ']; rfl
  have evo : ∀ k, σ'.victimOf k = σ.victimOf k := by intro k; rw [hσ']; rfl
  iintro ⟨Hσ, Hwlog, #Hcert, Hsy, Hun, Hvf, Hvs, Hvcap, %Hvlen, Hvbs, Hst, Hw, Hwo, Hmeta, #Hmfix,
    Hmem, #Hout, #Hm, #Hf, #Hc, #Hfo, Hev, Hl, #Hwf, Hcrt⟩
  unfold watchStoreBody
  rw [eL, eWs, eWu, eST, eWo, eM, evs, evbs, eVB]
  simp only [named]
  iframe Hσ Hwlog Hcert Hsy Hun Hvf Hvs Hvcap Hvbs Hwo Hmeta Hmfix
  isplitr
  · ipureintro; exact Hvlen
  isplitl [Hst Hw]
  · iapply (BigSepM.bigSepM_insert (m := σ.ST) hST).2
    iframe Hw Hst
  isplitl [Hmem Hev Hl Hcrt]
  · iapply (BigSepM.bigSepM_insert (m := σ.ST) hST).2
    isplitr [Hmem]
    · unfold memberRes
      iexists γw, r, fcs
      have hlw : σ'.live w := (hlv w).2 (Or.inl rfl)
      simp only [hlw, ↓reduceIte, eM]
      iframe Hm Hf Hc Hfo
      isplitr
      · ipureintro; exact hM
      isplitr
      · ipureintro; exact hsr
      iexists evsw, sint.nat st.minRev
      iframe Hev Hl
      isplitr
      · ipureintro; rw [eE, GMap.lookup_insert]
      have hz : (sint.nat st.minRev : Int) = sint.Z st.minRev := by
        show ((sint.Z st.minRev).toNat : Int) = _; omega
      unfold popFacts
      cases b
      · have h1 : (σ'.Ws !! w).isSome = false := by rw [eWs]; simp [hWs]
        have h2 : (σ'.Wu !! w).isSome = true := by rw [eWu]; simp [GMap.lookup_insert]
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
        iframe Hwf
        icases Hcrt with ⟨%Lc, #HLc, %hLc⟩
        isplitr
        · ipureintro; simp [hlo]
        iexists Lc
        iframe HLc
        ipureintro; exact hLc
      · have h1 : (σ'.Ws !! w).isSome = true := by rw [eWs]; simp [GMap.lookup_insert]
        simp only [h1, ↓reduceIte]
        iframe Hwf
        ipureintro; exact ⟨hlo, by omega⟩
    · iapply (BigSepM.bigSepM_mono (fun {k v} hk => ?_)) $$ Hmem
      have hk' : k ≠ w := by
        intro e; subst e
        have : σ.ST !! k = some v := hk
        rw [hST] at this; cases this
      apply mv_memberRes_congr γ 1 σ σ' k v eM
      · rw [eWs]; cases b <;> simp [GMap.lookup_insert_ne _ _ (Ne.symm hk'), Ne.symm hk']
      · rw [eWu]; cases b <;> simp [GMap.lookup_insert_ne _ _ (Ne.symm hk'), Ne.symm hk']
      · exact evo k
      · rw [eE, GMap.lookup_insert_ne _ _ (Ne.symm hk')]
  isplitr
  · icases (BigSepM.bigSepM_delete (m := σ.Wo) hwo).1 $$ Hout with ⟨-, Hrest⟩
    rw [mv_std_delete_eq]
    iapply (BigSepM.bigSepM_mono (fun {k v} _ => by unfold outRes; rw [eM])) $$ Hrest
  ipureintro; exact hok'

/-- A failed watcher's resources (out with the mover), as a victim under the lock again. -/
theorem mv_mover_to_member (γ : WsNames) (σ' : WsState) (w : Loc) (st : WatcherSt)
    (B : EventBatch) (evsw : List EvM) (hl : σ'.live w) (hWs : (σ'.Ws !! w).isSome = false)
    (hWu : (σ'.Wu !! w).isSome = false) (hv : σ'.victimOf w = some B)
    (hE : σ'.E !! w = some (evsw, sint.nat st.minRev)) (γw : WatcherNames)
    (hM' : σ'.M !! w = some γw) :
    moverResG (GF := GF) γ w st B evsw γw ⊢ watcherOwn w st (1 : Qp).half ∗ memberRes γ 1 σ' w st := by
  unfold moverResG
  iintro ⟨%r, %fcs, #Hm, #Hf, #Hc, #Hfo, %Hp, Hown, Hev, Hl, #Hwf⟩
  iframe Hown
  unfold memberRes popFacts
  simp only [hl, hWs, hWu, hv, ↓reduceIte, Bool.false_eq_true]
  iexists γw, r, fcs
  isplitr
  · ipureintro; exact hM'
  iframe Hm Hf Hc Hfo
  isplitr
  · ipureintro; exact Hp.1
  iexists evsw, sint.nat st.minRev
  iframe Hev Hl Hwf
  ipureintro; exact ⟨hE, Hp.2.1, rfl, Hp.2.2⟩

/-- The failed watchers are out in the lock's state, with the states the mover has. -/
theorem mv_nv_wo (γ : WsNames) (σ : WsState) (hok : WsOk σ) (NV : GMap Loc NvEnt) :
    ghostMapAuth (GF := GF) γ.wmeta 1 σ.M ∗ ([∗map] k ↦ v ∈ σ.ST, watcherOwn k v) ∗
      ([∗map] k ↦ v ∈ σ.Wo, watcherOwn k v (1 : Qp).half) ∗
      ([∗map] w ↦ x ∈ NV, moverResG γ w x.st x.B x.evsw x.γw) ⊢
    ⌜∀ w x, NV !! w = some x → σ.Wo !! w = some x.st ∧ σ.M !! w = some x.γw⌝ := by
  iintro ⟨Hmeta, Hst, Hwo, Hnv⟩
  iapply pure_forall.2
  iintro %w
  iapply pure_forall.2
  iintro %x
  by_cases h : NV !! w = some x
  · icases (BigSepM.bigSepM_lookup_acc (m := NV) h).1 $$ Hnv with ⟨Hx, -⟩
    unfold moverResG
    icases Hx with ⟨%r, %fcs, #Hm, -, -, -, -, Hown, -⟩
    ihave #Hm0 := Hm
    iunfold watcherMeta at Hm0
    ihave %HM := ghost_map_lookup $$ Hmeta Hm0
    ihave %H := mv_wo_lookup γ σ hok w x.γw x.st $$ [$Hmeta $Hm $Hst $Hwo $Hown]
    ipureintro; intro _; exact ⟨H, HM⟩
  · ipureintro; intro h'; exact absurd h' h

/-- **The failed watchers back as victims**, in one batch appended (`appendState`). -/
theorem body_append (s : Loc) (γ : WsNames) (σ σ' : WsState) (hok : WsOk σ) (NV : GMap Loc NvEnt)
    (vs' : GoSlice) (nvm : GoMap)
    (hNV2 : ∀ w x, NV !! w = some x → σ.Wo !! w = some x.st ∧ σ.M !! w = some x.γw)
    (hσ' : σ' = appendState σ NV vs' nvm) :
    ghostVar (GF := GF) γ.wst 1 σ' ∗
      ghostVar γ.wlog (1 : Qp).half σ.Lmu ∗ idxCert γ.st.idx σ.Lmu ∗
      ownWatcherGroup (syncedAddr s) σ.Ws ∗ ownWatcherGroup (unsyncedAddr s) σ.Wu ∗
      typedPointsto (victimsAddr s) vs' (DFrac.own 1) ∗ ownSlice vs' (σ.vbs ++ [nvm]) (DFrac.own 1) ∗
      ownSliceCap GoMap vs' (DFrac.own 1) ∗ ⌜σ.vbs.length = σ.VB.length⌝ ∗
      ([∗list] x ∈ σ.vbs.zip σ.VB, ownWatcherBatch x.1 x.2) ∗
      ([∗map] k ↦ v ∈ σ.ST, watcherOwn k v) ∗
      ([∗map] k ↦ v ∈ σ.Wo, watcherOwn k v (1 : Qp).half) ∗
      ghostMapAuth γ.wmeta 1 σ.M ∗
      ([∗map] k ↦ _γw ∈ σ.M, ∃ (r : WatchRange) (fcs : GoSlice), watcherFixed k r fcs) ∗
      ([∗map] k ↦ v ∈ σ.ST, memberRes γ 1 σ k v) ∗ ([∗map] k ↦ v ∈ σ.Wo, outRes γ σ k v) ∗
      nvm ↦$ GMap.fmap NvEnt.eb NV ∗
      ([∗map] _w ↦ x ∈ NV, ⌜x.eb ≠ null⌝ ∗ ownEventBatch x.eb x.B) ∗
      ([∗map] w ↦ x ∈ NV, moverResG γ w x.st x.B x.evsw x.γw) ⊢
    watchStoreBody s γ 1 σ' := by
  have hNV : ∀ w x, NV !! w = some x → σ.Wo !! w = some x.st := fun w x h => (hNV2 w x h).1
  have hok' : WsOk σ' := hσ' ▸ appendState_ok hok NV vs' nvm hNV
  have hvo : ∀ k, σ'.victimOf k = (σ.victimOf k).or ((NV !! k).map NvEnt.B) := by
    intro k; rw [hσ']; exact appendState_victimOf σ NV vs' nvm k
  have hout : ∀ w x, NV !! w = some x → σ.ST !! w = none ∧ ¬ σ.live w ∧ σ.Ws !! w = none ∧
      σ.Wu !! w = none ∧ σ.victimOf w = none ∧ σ.E !! w = none :=
    fun w x h => hok.out (hNV w x h)
  have eL : σ'.Lmu = σ.Lmu := by rw [hσ']; rfl
  have eWs : σ'.Ws = σ.Ws := by rw [hσ']; rfl
  have eWu : σ'.Wu = σ.Wu := by rw [hσ']; rfl
  have eST : σ'.ST = σ.ST ∪ GMap.fmap NvEnt.st NV := by rw [hσ']; rfl
  have eWo : σ'.Wo = GMap.filter (fun w _ => !(NV !! w).isSome) σ.Wo := by
    rw [hσ']; show GMap.filter _ σ.Wo = _
    congr 1; funext w _; cases NV !! w <;> rfl
  have eE : σ'.E = σ.E ∪ GMap.fmap (fun x => (x.evsw, sint.nat x.st.minRev)) NV := by rw [hσ']; rfl
  have eM : σ'.M = σ.M := by rw [hσ']; rfl
  have evs : σ'.vs = vs' := by rw [hσ']; rfl
  have evbs : σ'.vbs = σ.vbs ++ [nvm] := by rw [hσ']; rfl
  have eVB : σ'.VB = σ.VB ++ [GMap.fmap NvEnt.B NV] := by rw [hσ']; rfl
  have hdisj : ∀ k, (σ.ST !! k).isSome → GMap.fmap NvEnt.st NV !! k = none := by
    intro k hk
    rw [GMap.lookup_fmap]
    cases hn : NV !! k with
    | none => rfl
    | some x => rw [(hout k x hn).1] at hk; cases hk
  have hWoN : GMap.filter (fun w _ => (NV !! w).isSome) σ.Wo = GMap.fmap NvEnt.st NV := by
    apply GMap.ext; intro k
    show (σ.Wo !! k).filter (fun _ => (NV !! k).isSome) = (NV !! k).map NvEnt.st
    cases hn : NV !! k with
    | none => cases σ.Wo !! k <;> simp [Option.filter]
    | some x => rw [hNV k x hn]; simp [Option.filter]
  iintro ⟨Hσ, Hwlog, #Hcert, Hsy, Hun, Hvf, Hvs, Hvcap, %Hvlen, Hvbs, Hst, Hwo, Hmeta, #Hmfix,
    Hmem, #Hout, Hnvm, Hnvb, Hnv⟩
  icases (mv_bigSepM_split _ (fun w _ => (NV !! w).isSome) σ.Wo).1 $$ Hwo with ⟨HwoN, HwoR⟩
  ihave HwoN' : [∗map] k ↦ v ∈ GMap.fmap NvEnt.st NV, watcherOwn (GF := GF) k v (1 : Qp).half $$ [HwoN]
  · rw [← hWoN]; iexact HwoN
  ihave HnvO := (mv_bigSepM_fmap (fun k v => watcherOwn (GF := GF) k v (1 : Qp).half) NvEnt.st NV).1 $$ HwoN'
  ihave HnvM : [∗map] w ↦ x ∈ NV, iprop(watcherOwn w x.st (1 : Qp).half ∗ memberRes γ 1 σ' w x.st) $$ [Hnv]
  · iapply (BigSepM.bigSepM_mono (fun {k x} hk => ?_)) $$ Hnv
    have hk' : NV !! k = some x := hk
    obtain ⟨hST, hl, hWs, hWu, hv, hE⟩ := hout k x hk'
    apply mv_mover_to_member γ σ' k x.st x.B x.evsw
    · exact Or.inr (Or.inr (by rw [hvo, hv, hk']; rfl))
    · rw [eWs, hWs]; rfl
    · rw [eWu, hWu]; rfl
    · rw [hvo, hv, hk']; rfl
    · rw [eE, GMap.lookup_union, hE, GMap.lookup_fmap, hk']; rfl
    · rw [eM]; exact (hNV2 k x hk').2
  icases (mv_bigSepM_sep _ _ _).1 $$ HnvM with ⟨HnvO2, HnvMem⟩
  ihave HnvOwn : [∗map] k ↦ v ∈ GMap.fmap NvEnt.st NV, watcherOwn (GF := GF) k v $$ [HnvO HnvO2]
  · iapply (mv_bigSepM_fmap (fun k v => watcherOwn (GF := GF) k v) NvEnt.st NV).2
    ihave H := (mv_bigSepM_sep _ _ _).2 $$ [HnvO HnvO2]
    · iframe HnvO HnvO2
    iapply (BigSepM.bigSepM_mono (fun {k v} _ => (mv_watcherOwn_halves k v.st).2)) $$ H
  ihave HnvMem' : [∗map] k ↦ v ∈ GMap.fmap NvEnt.st NV, memberRes γ 1 σ' k v $$ [HnvMem]
  · iapply (mv_bigSepM_fmap (fun k v => memberRes (GF := GF) γ 1 σ' k v) NvEnt.st NV).2
    iexact HnvMem
  icases (mv_bigSepM_split _ (fun w _ => (NV !! w).isSome) σ.Wo).1 $$ Hout with ⟨-, #HoutR⟩
  unfold watchStoreBody
  rw [eL, eWs, eWu, eST, eWo, eM, evs, evbs, eVB]
  simp only [named]
  iframe Hσ Hwlog Hcert Hsy Hun Hvf Hvs Hvcap Hmeta Hmfix
  isplitr
  · ipureintro; simp [Hvlen]
  isplitl [Hvbs Hnvm Hnvb]
  · rw [List.zip_append Hvlen]
    iapply BigSepL.bigSepL_append.2
    iframe Hvbs
    simp only [List.zip_cons_cons, List.zip_nil_right]
    iapply BigSepL.bigSepL_singleton.2
    unfold ownWatcherBatch
    iexists GMap.fmap (fun x => (x.eb, x.B)) NV
    isplitl [Hnvm]
    · have : GMap.fmap Prod.fst (GMap.fmap (fun x : NvEnt => (x.eb, x.B)) NV) = GMap.fmap NvEnt.eb NV :=
        GMap.ext (fun k => by show ((NV !! k).map _).map _ = (NV !! k).map _; cases NV !! k <;> rfl)
      rw [this]; iexact Hnvm
    isplitr
    · ipureintro
      exact GMap.ext (fun k => by show (NV !! k).map _ = ((NV !! k).map _).map _; cases NV !! k <;> rfl)
    iapply (mv_bigSepM_fmap (fun _ p => iprop(⌜p.1 ≠ null⌝ ∗ ownEventBatch (GF := GF) p.1 p.2))
      (fun x : NvEnt => (x.eb, x.B)) NV).2
    iexact Hnvb
  isplitl [Hst HnvOwn]
  · iapply (mv_bigSepM_union _ σ.ST _ hdisj).2
    iframe Hst HnvOwn
  isplitl [HwoR]
  · iexact HwoR
  isplitl [Hmem HnvMem']
  · iapply (mv_bigSepM_union _ σ.ST _ hdisj).2
    iframe HnvMem'
    iapply (BigSepM.bigSepM_mono (fun {k v} hk => ?_)) $$ Hmem
    have hn : NV !! k = none := by
      cases h : NV !! k with
      | none => rfl
      | some x =>
        have := (hout k x h).1
        have hk' : σ.ST !! k = some v := hk
        rw [this] at hk'; cases hk'
    apply mv_memberRes_congr γ 1 σ σ' k v eM
    · rw [eWs]
    · rw [eWu]
    · rw [hvo, hn]; cases σ.victimOf k <;> rfl
    · rw [eE, GMap.lookup_union, GMap.lookup_fmap, hn]; cases σ.E !! k <;> rfl
  isplitr
  · iapply (BigSepM.bigSepM_mono (fun {k v} _ => by unfold outRes; rw [eM])) $$ HoutR
  ipureintro; exact hok'

/-- A watcher whose batch (at `p.1`, model `p.2`) the mover sent: the batch's struct (its
`moreRev` is read when the watcher goes back), and the mover's resources with the batch's events
delivered. -/
def sentW (γ : WsNames) (w : Loc) (p : Loc × EventBatch) : IProp GF :=
  iprop((∃ sl : GoSlice,
      p.1 ↦ ({ evs' := sl, revs' := p.2.revs, moreRev' := p.2.moreRev } : eventBatch)) ∗
    ∃ (st : WatcherSt) (evsw : List EvM) (γw : WatcherNames),
      moverResG γ w st ⟨[], p.2.revs, p.2.moreRev⟩ evsw γw)

/-- What `send` takes of a delivery (nothing for no events), and what is kept. -/
theorem mv_ev_pre (γ : WsNames) (γw : WatcherNames) (r : WatchRange) (evsw evs : List EvM) (d : Nat) :
    monoListAuthOwn (GF := GF) γw.evs (1 : Qp).half evsw ∗ evsWf γ r γw.lo (evsw ++ evs) d ⊢
      (if evs = [] then iprop(True) else
        monoListAuthOwn γw.evs (1 : Qp).half evsw ∗ evsWf γ r γw.lo (evsw ++ evs) d) ∗
      (if evs = [] then monoListAuthOwn γw.evs (1 : Qp).half evsw else iprop(True)) := by
  by_cases h : evs = []
  · simp only [h, ↓reduceIte]; iintro ⟨H, -⟩; iframe H
  · simp only [h, ↓reduceIte]; iintro ⟨H1, H2⟩; iframe H1 H2

/-- The delivered events after `send` (unchanged for no events). -/
theorem mv_ev_post (γw : WatcherNames) (evsw evs : List EvM) (ok : Bool) :
    (if evs = [] then iprop(True) else
        monoListAuthOwn (GF := GF) γw.evs (1 : Qp).half (if ok then evsw ++ evs else evsw)) ∗
      (if evs = [] then monoListAuthOwn γw.evs (1 : Qp).half evsw else iprop(True)) ⊢
    monoListAuthOwn γw.evs (1 : Qp).half (if ok then evsw ++ evs else evsw) := by
  by_cases h : evs = []
  · subst h; simp only [↓reduceIte, List.append_nil, ite_self]; iintro ⟨-, H⟩; iexact H
  · simp only [h, ↓reduceIte]; iintro ⟨H, -⟩; iexact H

end reprs

end mvcc
end EtcdGrove
end Perennial
