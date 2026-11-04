/-
The page store's invariant and its lemmas (U0a of `notes/bbolt-proof-plan.md`; design §3.6):
`pagesInv`, the store slots' cells (lent at `rq` to readers and at `wq` to the writer) and
page-cache bytes, the meta cells' lending (`metaLend`, minibolt's `metaLent`), and the fancy
updates at `pagesN N` that the protocols take (U3 proves them).

Each lemma takes the invariant and the caller's shares of the agreed ghost state, and gives them
back updated; slots moving between the store and the writer's `W` slots move with their cells
and bytes (`slotsOwn`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section store
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The store slots of a committed state and a freelist (`storeSlots σ = slotsOf σ.C σ.fl`). -/
def slotsOf (C : CommitSt) (fl : FLPg) : List Nat := listDedup (treeSlots C ++ pendSlots fl)

/-- A view's cells at the fraction `q`: page `id` at `base + 4096 · id`. -/
def viewCells (q : Qp) (v : View) : IProp GF :=
  iprop([∗map] id ↦ pg ∈ v.pages, bytesPointsto (v.base +ₗ ((id * 4096 : Nat) : Int)) (DFrac.own q) pg)

/-- The page-cache bytes of slot `s` of the file `p`, all of them, holding `bs`. -/
def osSlot (p : GoString) (s : Nat) (bs : List w8) : IProp GF :=
  iprop(∃ xs : List (w8 × Bool), osBytes p (4096 * s) (DFrac.own 1) xs ∗ ⌜xs.map Prod.fst = bs⌝)

/-- The slots `S` whole, as they move between the store and `W`: their client cell halves (when
mapped) and their page-cache bytes, holding `bs`. -/
def slotsOwn (ms : MapSt) (p : GoString) (S : List Nat) (bs : Nat → List w8) : IProp GF :=
  iprop([∗list] s ∈ S, (match ms with
      | some (base, _) => bytesPointsto (base +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s)
      | none => iprop(emp)) ∗
    osSlot p s (bs s))

/-- **The store slots' cells**: per slot `s`, `e_s` of the client half held here, the rest
(`lent σ s`) lent; nothing while unmapped. -/
def storeCells (σ : StoreSt) : IProp GF :=
  match σ.ms with
  | none => iprop(emp)
  | some (base, _) => iprop([∗list] s ∈ storeSlots σ,
      ∃ e : Qp, ⌜fracSum e (lent σ s) (1 : Qp).half⌝ ∗
        bytesPointsto (base +ₗ ((4096 * s : Nat) : Int)) (DFrac.own e) (σ.bytes s))

/-- **The meta cells' lend quarter**: home (with the loan token `mln`); out with the writer
(during the meta write, which deposits `mlk`, with `mln`); or lent to the one reader holding
`metalock`, which deposits `mlk` and `mtok (rfrac/2)` and holds `mln` (U3 finding 10, as
minibolt's loan tokens). -/
def metaLend (B : BNs) (σ : StoreSt) : IProp GF :=
  iprop((metaCellsQ (1 : Qp).half.half σ.ms σ.C ∗ ghostVar B.out (1 : Qp).half false ∗
      ghostVar B.mln 1 ()) ∨
    (ghostVar B.out (1 : Qp).half true ∗ ghostVar B.mlk 1 () ∗ ghostVar B.mln 1 ()) ∨
    (ghostVar B.out (1 : Qp).half false ∗ ghostVar B.mlk 1 () ∗
      ghostVar B.mtok sync.rfrac.half ()))

/-- **The store slots' bytes, as a ghost witness** `W` (U3 finding 11): half here, the other half
here too while mapped (`store_gather` hands it out with the cells, `store_carve` takes both
back, so that the new mapping's cells are known to hold the store's bytes). -/
def bytesWit (B : BNs) (σ : StoreSt) (W : GMap Nat (List w8)) : IProp GF :=
  iprop(ghostVar B.byt (1 : Qp).half W ∗
    (match σ.ms with
     | some _ => ghostVar B.byt (1 : Qp).half W
     | none => iprop(emp)) ∗
    ⌜∀ s ∈ storeSlots σ, W !! s = some (σ.bytes s)⌝)

/-- **The page store's invariant** (design §3.6). -/
def pagesInv (B : BNs) (p : GoString) : IProp GF :=
  iprop(∃ (σ : StoreSt) (W : GMap Nat (List w8)),
    ghostVar B.cur (1 : Qp).half.half σ.C ∗ ghostVar B.fl (1 : Qp).half σ.fl ∗
    ghostVar B.map (1 : Qp).half.half σ.ms ∗ ghostVar B.wv (1 : Qp).half σ.wst ∗
    ghostMapAuth B.rds 1 σ.R ∗
    ([∗map] k ↦ r ∈ σ.R, k ↪[B.fltx] (W64 (r.v.txid : Int)) ∗ ghostVar B.mtok sync.rfrac ()) ∗
    storeCells σ ∗ ([∗list] s ∈ storeSlots σ, osSlot p s (σ.bytes s)) ∗ bytesWit B σ W ∗
    metaLend B σ ∗ ⌜storeOK σ⌝)

/-! ## Lemma statements (U3), fancy updates at `pagesN N` -/

omit go_gctx sem in
private theorem pagesInv_timeless (B : BNs) (p : GoString) : Timeless (pagesInv (GF := GF) B p) := by
  have h1 : ∀ σ : StoreSt, Timeless (storeCells (GF := GF) σ) := by
    intro σ; unfold storeCells; split <;> infer_instance
  have h2 : ∀ σ : StoreSt, Timeless (metaLend (GF := GF) B σ) := by
    intro σ; unfold metaLend metaCellsQ; split <;> infer_instance
  have h4 : ∀ σ W, Timeless (bytesWit (GF := GF) B σ W) := by
    intro σ W; unfold bytesWit; split <;> infer_instance
  have h3 : ∀ s bs, Timeless (osSlot (GF := GF) p s bs) := by
    intro s bs
    have : ∀ off dq xs, Timeless (osBytes (GF := GF) p off dq xs) := fun _ _ _ => by
      unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
    unfold osSlot; infer_instance
  unfold pagesInv
  infer_instance

section helpers
set_option linter.unusedSectionVars false

/-- A slot's cell at fraction `e`. -/
private abbrev slotPt (base : Loc) (bytes : Nat → List w8) (s : Nat) (e : Qp) : IProp GF :=
  bytesPointsto (base +ₗ ((4096 * s : Nat) : Int)) (DFrac.own e) (bytes s)

private theorem slotPt_add (base : Loc) (bytes : Nat → List w8) (s : Nat) (a b : Qp) :
    slotPt (GF := GF) base bytes s (a + b) ⊣⊢ slotPt base bytes s a ∗ slotPt base bytes s b :=
  (bytesPointsto_dfractional (GF := GF) _ _).dfractional (DFrac.own a) (DFrac.own b)

/-- A page's cells are its slots' cells. -/
private theorem page_slots (base : Loc) (dq : DFrac) (bytes : Nat → List w8) :
    ∀ (n id : Nat), (∀ j, id ≤ j → j < id + n → (bytes j).length = 4096) →
    bytesPointsto (GF := GF) (base +ₗ ((id * 4096 : Nat) : Int)) dq
        ((List.range' id n).flatMap bytes) ⊣⊢
      [∗list] j ∈ List.range' id n, bytesPointsto (base +ₗ ((4096 * j : Nat) : Int)) dq (bytes j)
  | 0, id, _ => by
    simp only [List.range'_zero, List.flatMap_nil]
    unfold bytesPointsto
    exact ⟨by iintro -; iapply BigSepL.bigSepL_nil.2; iempintro,
      by iintro -; ipureintro; trivial⟩
  | n + 1, id, hl => by
    have ih := page_slots base dq bytes n (id + 1) (fun j h1 h2 => hl j (by omega) (by omega))
    rw [List.range'_succ, List.flatMap_cons]
    refine (bytesPointsto_app _ _ _ _).trans ?_
    rw [hl id (by omega) (by omega)]
    have e1 : base +ₗ ((id * 4096 : Nat) : Int) +ₗ ((4096 : Nat) : Int) =
        base +ₗ (((id + 1) * 4096 : Nat) : Int) := by
      rw [loc_add_assoc]; exact congrArg (base +ₗ ·) (by omega)
    have e2 : ((id * 4096 : Nat) : Int) = ((4096 * id : Nat) : Int) := by omega
    rw [e1, e2]
    exact (sep_congr .rfl ih).trans (BigSepL.bigSepL_cons
      (Φ := fun _ j => bytesPointsto (GF := GF) (base +ₗ ((4096 * j : Nat) : Int)) dq (bytes j))).symm

private theorem bigSepL_ite_mem (X : Nat → IProp GF) (T : List Nat) :
    ∀ S : List Nat, ([∗list] s ∈ S, if s ∈ T then X s else iprop(emp)) ⊣⊢
      [∗list] s ∈ S.filter (fun s => decide (s ∈ T)), X s
  | [] => by simp only [List.filter_nil]; exact .rfl
  | a :: S => by
    have ih := bigSepL_ite_mem X T S
    refine (BigSepL.bigSepL_cons (Φ := fun _ s => if s ∈ T then X s else iprop(emp))).trans ?_
    by_cases ha : a ∈ T
    · simp only [List.filter_cons, ha, decide_true, ite_true]
      exact (sep_congr .rfl ih).trans (BigSepL.bigSepL_cons (Φ := fun _ s => X s)).symm
    · simp only [List.filter_cons, ha, decide_false, ite_false, Bool.false_eq_true]
      exact (sep_congr .rfl ih).trans emp_sep

private theorem bigSepL_sub (X : Nat → IProp GF) (S T : List Nat) (hS : S.Nodup) (hT : T.Nodup)
    (hsub : ∀ x ∈ T, x ∈ S) :
    ([∗list] s ∈ S, if s ∈ T then X s else iprop(emp)) ⊣⊢ [∗list] s ∈ T, X s := by
  refine (bigSepL_ite_mem X T S).trans (BigSepL.bigSepL_perm ?_)
  refine (List.perm_ext_iff_of_nodup (hS.filter _) hT).2 fun x => ?_
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hsub x h, h⟩⟩

private theorem fracSum_optAdd (e q h : Qp) (x : Option Qp) :
    fracSum e (optAdd q x) h ↔ fracSum (e + q) x h := by
  cases x <;> simp only [fracSum, optAdd]
  rw [Qp.ext_iff, Qp.ext_iff]; simp only [Qp.val_add]; grind

private theorem bigSepL_mono_mem {Φ Ψ : Nat → IProp GF} {S : List Nat} (h : ∀ s ∈ S, Φ s ⊢ Ψ s) :
    ([∗list] s ∈ S, Φ s) ⊢ [∗list] s ∈ S, Ψ s :=
  BigSepL.bigSepL_mono fun {_ _} hk => h _ (List.mem_of_getElem? hk)

/-- Returning `q` of each slot of `T ⊆ S`. -/
private theorem cells_return (S T : List Nat) (hS : S.Nodup) (hT : T.Nodup) (hsub : ∀ x ∈ T, x ∈ S)
    (A : Nat → Qp → IProp GF) (hA : ∀ s a b, A s (a + b) ⊣⊢ A s a ∗ A s b)
    (L L' : Nat → Option Qp) (q h : Qp)
    (hL : ∀ s ∈ S, L s = if s ∈ T then optAdd q (L' s) else L' s) :
    ([∗list] s ∈ S, ∃ e, ⌜fracSum e (L s) h⌝ ∗ A s e) ∗ ([∗list] s ∈ T, A s q) ⊢
      [∗list] s ∈ S, ∃ e, ⌜fracSum e (L' s) h⌝ ∗ A s e := by
  refine (sep_mono .rfl (bigSepL_sub (fun s => A s q) S T hS hT hsub).2).trans ?_
  refine BigSepL.bigSepL_sep_eqv.2.trans (bigSepL_mono_mem fun s hs => ?_)
  have hLs := hL s hs
  by_cases hsT : s ∈ T
  · simp only [hsT, ite_true] at hLs ⊢
    iintro ⟨⟨%e, %he, Ha⟩, Hq⟩
    iexists (e + q)
    isplitr
    · ipureintro; rw [hLs, fracSum_optAdd] at he; exact he
    · iapply (hA s e q).2; iframe
  · simp only [hsT, ite_false] at hLs ⊢
    iintro ⟨⟨%e, %he, Ha⟩, -⟩
    iexists e; rw [hLs] at he; iframe; ipureintro; exact he

private theorem cells_borrow_one (T : List Nat) (A : Nat → Qp → IProp GF)
    (hA : ∀ s a b, A s (a + b) ⊣⊢ A s a ∗ A s b) (L L' : Nat → Option Qp) (q h : Qp) (s : Nat)
    (hLs : L' s = if s ∈ T then optAdd q (L s) else L s)
    (hpos : s ∈ T → ∀ x, L' s = some x → x < h) : (∃ e, ⌜fracSum e (L s) h⌝ ∗ A s e) ⊢
      (∃ e, ⌜fracSum e (L' s) h⌝ ∗ A s e) ∗ (if s ∈ T then A s q else iprop(emp)) := by
  by_cases hsT : s ∈ T
  · simp only [hsT, ite_true] at hLs ⊢
    have hp := hpos hsT
    iintro ⟨%e, %he, Ha⟩
    have hlt : q < e := by
      rcases hx : L s with _ | y
      · rw [hx] at he hLs
        have he2 : e = h := he
        subst he2
        exact hp q (by rw [hLs]; rfl)
      · rw [hx] at he hLs
        have he2 : e + y = h := he
        have := hp (q + y) (by rw [hLs]; rfl)
        subst he2
        rw [Qp.lt_iff] at this ⊢; simp only [Qp.val_add] at this; grind
    obtain ⟨e', he'⟩ := Qp_split_lt q e hlt
    subst he'
    icases (hA s q e').1 $$ Ha with ⟨Hq, He⟩
    isplitl [He]
    · iexists e'
      iframe
      ipureintro
      rw [hLs, fracSum_optAdd]
      have hc : e' + q = q + e' := by rw [Qp.ext_iff]; simp only [Qp.val_add]; grind
      rw [hc]; exact he
    · iexact Hq
  · simp only [hsT, ite_false] at hLs ⊢
    iintro ⟨%e, %he, Ha⟩
    isplitl
    · iexists e; rw [hLs]; iframe; ipureintro; exact he
    · iempintro

/-- Borrowing `q` of each slot of `T ⊆ S`, when what is then lent stays below `h`. -/
private theorem cells_borrow (S T : List Nat) (hS : S.Nodup) (hT : T.Nodup) (hsub : ∀ x ∈ T, x ∈ S)
    (A : Nat → Qp → IProp GF) (hA : ∀ s a b, A s (a + b) ⊣⊢ A s a ∗ A s b)
    (L L' : Nat → Option Qp) (q h : Qp)
    (hL : ∀ s ∈ S, L' s = if s ∈ T then optAdd q (L s) else L s)
    (hpos : ∀ s ∈ T, ∀ x, L' s = some x → x < h) :
    ([∗list] s ∈ S, ∃ e, ⌜fracSum e (L s) h⌝ ∗ A s e) ⊢
      ([∗list] s ∈ S, ∃ e, ⌜fracSum e (L' s) h⌝ ∗ A s e) ∗ ([∗list] s ∈ T, A s q) := by
  have key : ∀ s ∈ S, (∃ e, ⌜fracSum e (L s) h⌝ ∗ A s e) ⊢
      (∃ e, ⌜fracSum e (L' s) h⌝ ∗ A s e) ∗ (if s ∈ T then A s q else iprop(emp)) := by
    intro s hs
    exact cells_borrow_one T A hA L L' q h s (hL s hs) (fun hT => hpos s hT)
  refine (bigSepL_mono_mem key).trans ?_
  refine BigSepL.bigSepL_sep_eqv.1.trans ?_
  exact sep_mono .rfl (bigSepL_sub (fun s => A s q) S T hS hT hsub).1

private theorem mem_pagesSlots (P : Pages) (s : Nat) : s ∈ pagesSlots P ↔ coversSlot P s := by
  simp only [pagesSlots, List.mem_flatMap, List.mem_range', coversSlot]
  constructor
  · rintro ⟨⟨id, pg⟩, hip, j, hj, rfl⟩
    exact ⟨id, pg, (GMap.mem_toList _ _ _).1 hip, by omega, by simp only at hj; omega⟩
  · rintro ⟨id, pg, hp, h1, h2⟩
    exact ⟨(id, pg), (GMap.mem_toList _ _ _).2 hp, s - id, by simp only; omega, by omega⟩

private theorem pagesSlots_nodup (P : Pages) (hd : pagesDisjoint P) : (pagesSlots P).Nodup := by
  unfold pagesSlots List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun a _ => List.nodup_range', ?_⟩
  have hk := GMap.toList_keys_nodup P
  rw [List.Nodup, List.pairwise_map] at hk
  refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.and_mem.1 hk)
  intro a b ha hb hne x hx y hy hxy
  subst hxy
  simp only [List.mem_range'] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, hij⟩ := hy
  rcases hd a.1 a.2 b.1 b.2 ((GMap.mem_toList _ _ _).1 ha) ((GMap.mem_toList _ _ _).1 hb)
    hne.2.2 with h | h <;> omega

/-- A view's cells are its slots' cells. -/
private theorem viewCells_slots (q : Qp) (v : View) (bytes : Nat → List w8)
    (hPF : pagesFromBytes bytes v.pages)
    (hlen : ∀ s, coversSlot v.pages s → (bytes s).length = 4096) :
    viewCells (GF := GF) q v ⊣⊢ [∗list] s ∈ pagesSlots v.pages, slotPt v.base bytes s q := by
  unfold viewCells pagesSlots
  rw [BigSepL.bigSepL_flatMap]
  refine (BigSepM.bigSepM_toList).trans ⟨BigSepL.bigSepL_mono fun {k x} hk => ?_,
    BigSepL.bigSepL_mono fun {k x} hk => ?_⟩
  all_goals
    have hx := (GMap.mem_toList _ _ _).1 (List.mem_of_getElem? hk)
    have hpg := hPF x.1 x.2 hx
    have hl : ∀ j, x.1 ≤ j → j < x.1 + (1 + pageOverflow x.2) → (bytes j).length = 4096 :=
      fun j h1 h2 => hlen j ⟨x.1, x.2, hx, h1, h2⟩
    have := page_slots (GF := GF) v.base (DFrac.own q) bytes (1 + pageOverflow x.2) x.1 hl
  · conv => lhs; rw [hpg]
    exact this.1
  · conv => rhs; rw [hpg]
    exact this.2

private theorem storeCells_some (σ : StoreSt) (b : Loc) (l : Nat) (hms : σ.ms = some (b, l)) :
    storeCells (GF := GF) σ =
      [∗list] s ∈ storeSlots σ,
        iprop(∃ e, ⌜fracSum e (lent σ s) (1 : Qp).half⌝ ∗ slotPt b σ.bytes s e) := by
  unfold storeCells; rw [hms]

/-- A view in the store: its slots, distinct, are store slots of 4096 bytes. -/
private theorem view_slots (σ : StoreSt) (h : storeOK σ) (v : View) (hin : viewInStore σ v)
    (hwf : viewWF v) :
    (pagesSlots v.pages).Nodup ∧ (∀ x ∈ pagesSlots v.pages, x ∈ storeSlots σ) ∧
      ∀ s, coversSlot v.pages s → (σ.bytes s).length = 4096 := by
  obtain ⟨C, hC, hv⟩ := hwf
  refine ⟨?_, fun x hx => hin x ((mem_pagesSlots _ _).1 hx),
    fun s hs => (h.2.2.2.2.2.2.2.2.2.2.2.1 s (hin s hs)).2⟩
  rw [← hv]; exact pagesSlots_nodup _ hC.2.2.1

open Classical in
private theorem lent_fold_le2 (s : Nat) (l : List (Nat × RdInfo)) (q : Qp)
    (h : l.foldr (fun kv acc => if coversSlot kv.2.v.pages s then optAdd rq acc else acc) none
      = some q) : q.val ≤ (l.length : Rat) * rq.val := by
  induction l generalizing q with
  | nil => simp at h
  | cons kv l ih =>
    simp only [List.foldr_cons] at h
    have hq := rq.2
    split at h
    · revert h
      generalize hf : List.foldr _ none l = r
      intro h
      cases r with
      | none =>
        simp only [optAdd, Option.some.injEq] at h; subst h
        simp only [List.length_cons]; push_cast
        have : (0 : Rat) ≤ (l.length : Rat) * rq.val :=
          Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (by grind)
        grind
      | some b =>
        simp only [optAdd, Option.some.injEq] at h; subst h
        have := ih b hf
        simp only [List.length_cons, Qp.val_add]; push_cast
        grind
    · have := ih q h
      simp only [List.length_cons]; push_cast
      grind

/-- What is lent of a slot, when the readers' deposits fit in `mtok`'s whole. -/
private theorem lent_lt_half2 (σ : StoreSt) (hsz : (σ.R.size : Rat) * sync.rfrac.val ≤ 1) (s : Nat)
    (x : Qp) (h : lent σ s = some x) : x < (1 : Qp).half := by
  classical
  have hrq : rq.val = sync.rfrac.val / 4 := by
    simp only [rq, Qp.val_half]; grind
  have hwq : wq.val = 1 / 8 := by simp only [wq, Qp.val_half, Qp.val_one]; grind
  have hr : ∀ q', GMap.mapFold (fun _ (ri : RdInfo) acc =>
      if coversSlot ri.v.pages s then optAdd rq acc else acc) none σ.R = some q' →
      q'.val ≤ 1 / 4 := by
    intro q' hq'
    have := lent_fold_le2 s σ.R.toList q' hq'
    have hl : (σ.R.toList.length : Rat) = (σ.R.size : Rat) := rfl
    rw [hl, hrq] at this
    grind
  rw [Qp.lt_iff, Qp.val_half, Qp.val_one]
  unfold lent at h
  revert h
  generalize hf : GMap.mapFold _ none σ.R = r
  intro h
  have hqpos := x.2
  split at h
  · split at h
    · cases r with
      | none =>
        simp only [optAdd, Option.some.injEq] at h; subst h; rw [hwq]
        show (1 : Rat) / 8 < 1 / 2; grind
      | some b =>
        simp only [optAdd, Option.some.injEq] at h; subst h
        have := hr b hf; simp only [Qp.val_add]; rw [hwq]; grind
    · subst h; have := hr x hf; grind
  · subst h; have := hr x hf; grind

private theorem sep_keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (and_intro h .rfl).trans (pure_elim_left fun hφ => by iintro H; iframe; ipureintro; exact hφ)

private theorem ghostVar_le_one' (γ : GName) (q : Qp) :
    ghostVar (GF := GF) γ q () ⊢ ⌜q.val ≤ 1⌝ := by
  iintro H
  have hq : q = q.half + q.half := (Qp.half_add_half q).symm
  rw [hq]
  icases ((ghostVar_fractional (GF := GF) γ ()).fractional q.half q.half).1 $$ H with ⟨H1, H2⟩
  ihave %Hv := ghostVar_valid_2 γ () q.half () q.half $$ H1 H2
  ipureintro
  have := Hv.1
  rw [Qp.le_iff] at this; simp only [Qp.val_add, Qp.val_one] at this; exact this

private theorem deposits_le_aux {V : Type} (X : Nat → V → IProp GF) (γ : GName) (q : Qp) :
    ∀ m : GMap Nat V, ∀ Q : Qp, ([∗map] k ↦ r ∈ m, X k r ∗ ghostVar γ q ()) ∗ ghostVar γ Q () ⊢
      ⌜(m.size : Rat) * q.val + Q.val ≤ 1⌝ := by
  intro m
  induction m using GMap.map_ind with
  | h0 =>
    intro Q
    iintro ⟨-, H⟩
    ihave %h := ghostVar_le_one' γ Q $$ H
    ipureintro; rw [GMap.map_size_empty]; grind
  | hins k v m hk ih =>
    intro Q
    iintro ⟨Hm, HQ⟩
    icases (BigSepM.bigSepM_insert (Φ := fun k r => iprop(X k r ∗ ghostVar γ q ())) hk).1 $$ Hm
      with ⟨⟨-, Hq⟩, Hm⟩
    icases ((ghostVar_fractional (GF := GF) γ ()).fractional q Q).2 $$ [Hq HQ] with HqQ
    · iframe
    ihave %h := ih (q + Q) $$ [Hm HqQ]
    · iframe
    ipureintro
    rw [GMap.map_size_insert_None _ _ _ hk]; push_cast
    simp only [Qp.val_add] at h
    grind

private theorem deposits_le {V : Type} (X : Nat → V → IProp GF) (γ : GName) (q : Qp) (m : GMap Nat V) :
    ([∗map] k ↦ r ∈ m, X k r ∗ ghostVar γ q ()) ⊢ ⌜(m.size : Rat) * q.val ≤ 1⌝ := by
  induction m using GMap.map_ind with
  | h0 => iintro -; ipureintro; rw [GMap.map_size_empty]; grind
  | hins k v m hk _ =>
    iintro Hm
    icases (BigSepM.bigSepM_insert (Φ := fun k r => iprop(X k r ∗ ghostVar γ q ())) hk).1 $$ Hm
      with ⟨⟨-, Hq⟩, Hm⟩
    ihave %h := deposits_le_aux X γ q m q $$ [Hm Hq]
    · iframe
    ipureintro
    rw [GMap.map_size_insert_None _ _ _ hk]; push_cast
    grind

private theorem storeOK_wborrow_some (σ : StoreSt) (v : View) (b : Loc) (l : Nat) (h : storeOK σ)
    (hwv : σ.wv = some v) (hms : σ.ms = some (b, l)) : storeOK (σ.wborrow b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have hw' : (σ.wborrow b).wv = some { v with base := b } := by
    simp [StoreSt.wborrow, hwv]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun v' hv' => ?_, h9, fun k r hr => ⟨(h10 k r hr).1,
      fun v' hv' => ?_⟩, fun v' hv' => ?_, h12, h13, fun hm => ?_, fun hm => ?_,
    fun hw => ?_, h17⟩
  · rw [hw'] at hv'; cases hv'
    obtain ⟨a, b1, c, ⟨C, hC, hv⟩, e, f, -⟩ := h8 v hwv
    refine ⟨a, b1, c, ⟨C, hC, ?_⟩, e, f, fun _ b' l' hb => ?_⟩
    · rw [← hv]; rfl
    · simp only [StoreSt.wborrow, hms, Option.some.injEq, Prod.mk.injEq] at hb
      exact hb.1
  · rw [hw'] at hv'; cases hv'; exact (h10 k r hr).2 v hwv
  · rw [hw'] at hv'; cases hv'; exact h11 v hwv
  · simp [StoreSt.wborrow, hms] at hm
  · rw [hw'] at hm; cases hm
  · rw [h16 hw] at hwv; cases hwv

open Classical in
private theorem lent_deregister (σ : StoreSt) (k : Nat) (r : RdInfo) (hk : σ.R !! k = some r) (s : Nat) :
    lent σ s = if s ∈ pagesSlots r.v.pages then optAdd rq (lent (σ.deregister k) s)
      else lent (σ.deregister k) s := by
  have hR : σ.R = <[k := r]> (σ.R.delete k) := by
    rw [GMap.insert_delete, GMap.insert_id _ _ _ hk]
  have hfold := GMap.mapFold_insert (fun _ (ri : RdInfo) acc =>
      if coversSlot ri.v.pages s then optAdd rq acc else acc) none (σ.R.delete k) k r
    (fun j1 z1 j2 z2 y => by
      by_cases h1 : coversSlot z1.v.pages s <;> by_cases h2 : coversSlot z2.v.pages s <;>
        simp [h1, h2])
    (GMap.lookup_delete _ _)
  rw [← hR] at hfold
  have hcomm : ∀ (a b : Qp) (x : Option Qp), optAdd a (optAdd b x) = optAdd b (optAdd a x) := by
    intro a b x; cases x <;> simp only [optAdd, Option.some.injEq] <;>
      rw [Qp.ext_iff] <;> simp only [Qp.val_add] <;> grind
  unfold lent
  simp only [StoreSt.deregister]
  rw [hfold]
  by_cases hc : coversSlot r.v.pages s
  · simp only [hc, ite_true, (mem_pagesSlots _ _).2 hc]
    split
    · split <;> simp [hcomm]
    · rfl
  · have : s ∉ pagesSlots r.v.pages := fun h => hc ((mem_pagesSlots _ _).1 h)
    simp only [hc, ite_false, this]

end helpers

section lemmas
variable (B : BNs) (N : Namespace) (p : GoString) (E : CoPset) (hE : ↑(pagesN N) ⊆ E)
include hE

/-- `beginTx`, under `metalock` (`metaR`'s `cur`) and `Pm rfrac` (its `map` share and `mtok`):
register the reader `k` (its `fltx` fragment, inserted by the caller in `metaR`'s auth) with the
view of `C` at the mapping, borrowing `rq` of each of its slots and depositing `mtok rfrac`. -/
theorem store_register (C : CommitSt) (b : Loc) (l k : Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗ ghostVar B.mtok sync.rfrac () ∗
      k ↪[B.fltx] (W64 (C.txid : Int)) ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗
      k ↪[B.rds] (⟨View.ofC b C⟩ : RdInfo) ∗ viewCells rq (View.ofC b C) := by
  sorry

/-- `removeTx`, before `RUnlock`: deregister the reader `k`, its cells back; the deposits
returned. -/
theorem store_deregister (k : Nat) (r : RdInfo) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ k ↪[B.rds] r ∗ viewCells rq r.v ⊢
    |={E}=> ghostVar B.mtok sync.rfrac () ∗ k ↪[B.fltx] (W64 (r.v.txid : Int)) := by
  iintro ⟨#Hinv, Hk, Hv⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  ihave %hk := ghost_map_lookup $$ Hrds Hk
  have hk' : σ.R !! k = some r := hk
  have hrok := Hok.2.2.2.2.2.2.1 k r hk'
  obtain ⟨b, l, hms⟩ : ∃ b l, σ.ms = some (b, l) := by
    rcases hm : σ.ms with _ | ⟨b, l⟩
    · have := (Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hm).1
      rw [this] at hk'; simp at hk'
    · exact ⟨b, l, rfl⟩
  have hbase : r.v.base = b := hrok.2.2.2.2.2 b l hms
  obtain ⟨hTn, hTs, hTl⟩ := view_slots σ Hok r.v hrok.2.2.1 hrok.2.2.2.1
  imod ghost_map_delete $$ Hrds Hk with Hrds
  icases (BigSepM.bigSepM_delete
    (Φ := fun k' (r' : RdInfo) => iprop(k' ↪[B.fltx] (W64 (r'.v.txid : Int)) ∗
      ghostVar B.mtok sync.rfrac ())) hk').1 $$ Hdep with ⟨⟨Hf, Ht⟩, Hdep⟩
  ihave Hv := (viewCells_slots rq r.v σ.bytes hrok.2.2.2.2.1 hTl).1 $$ Hv
  rw [hbase]
  rw [storeCells_some σ b l hms]
  ihave Hcells := cells_return (storeSlots σ) (pagesSlots r.v.pages) (nodup_list_dedup _) hTn hTs
    (slotPt b σ.bytes) (slotPt_add b σ.bytes) (lent σ) (lent (σ.deregister k)) rq (1 : Qp).half
    (fun s _ => lent_deregister σ k r hk' s)
    $$ [Hcells Hv]
  · iframe
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.deregister k, W
    rw [storeCells_some (σ.deregister k) b l hms]
    have e2 : metaLend (GF := GF) B (σ.deregister k) = metaLend B σ := rfl
    have e3 : bytesWit (GF := GF) B (σ.deregister k) W = bytesWit B σ W := rfl
    rw [e2, e3]
    iframe
    ipureintro
    exact storeOK_deregister σ k Hok
  imodintro; iframe

/-- The writer's begin (after `store_release`): its txid the next, its base view (`C`'s at the
mapping) borrowed at `wq`. -/
theorem store_wbegin (C : CommitSt) (b : Loc) (l : Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗ ghostVar B.wv (1 : Qp).half wIdle ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      ghostVar B.wv (1 : Qp).half ((some (View.ofC b C), some (C.txid + 1), false, true) : WSt) ∗
      viewCells wq (View.ofC b C) := by
  sorry

/-- The remap: the writer's view returned (parked) before `munmap`. -/
theorem store_wreturn (v : View) (w : Option Nat) (pb : Bool) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗
      ghostVar B.wv (1 : Qp).half ((some v, w, pb, true) : WSt) ∗ viewCells wq v ⊢
    |={E}=> ghostVar B.wv (1 : Qp).half ((some v, w, pb, false) : WSt) := by
  iintro ⟨#Hinv, Hwv, Hv⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  simp only [StoreSt.wst, Prod.mk.injEq] at hws
  obtain ⟨hwv, hwtx, hpb, hwl⟩ := hws
  obtain ⟨b, l, hms⟩ : ∃ b l, σ.ms = some (b, l) := by
    rcases hm : σ.ms with _ | ⟨b, l⟩
    · have := (Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hm).2; rw [← hwl] at this; cases this
    · exact ⟨b, l, rfl⟩
  have hwok := Hok.2.2.2.2.2.2.2.1 v hwv.symm
  have hbase : v.base = b := hwok.2.2.2.2.2.2 hwl.symm b l hms
  obtain ⟨hTn, hTs, hTl⟩ := view_slots σ Hok v hwok.2.2.1 hwok.2.2.2.1
  imod ghostVar_update_halves ((some v, w, pb, false) : WSt) B.wv _ _ $$ Hwv Hwv' with ⟨Hwv, Hwv'⟩
  ihave Hv := (viewCells_slots wq v σ.bytes hwok.2.2.2.2.1 hTl).1 $$ Hv
  rw [hbase]
  rw [storeCells_some σ b l hms]
  ihave Hcells := cells_return (storeSlots σ) (pagesSlots v.pages) (nodup_list_dedup _) hTn hTs
    (slotPt b σ.bytes) (slotPt_add b σ.bytes) (lent σ) (lent σ.wreturn) wq (1 : Qp).half
    (fun s _ => by
      unfold lent; rw [← hwv, ← hwl]
      simp only [StoreSt.wreturn]
      by_cases hc : coversSlot v.pages s
      · simp [hc, (mem_pagesSlots _ _).2 hc]
      · simp [hc, show s ∉ pagesSlots v.pages from fun h => hc ((mem_pagesSlots _ _).1 h)])
    $$ [Hcells Hv]
  · iframe
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.wreturn, W
    rw [storeCells_some σ.wreturn b l hms]
    have e2 : metaLend (GF := GF) B σ.wreturn = metaLend B σ := rfl
    have e3 : bytesWit (GF := GF) B σ.wreturn W = bytesWit B σ W := rfl
    rw [e2, e3]
    have ew : σ.wreturn.wst = ((some v, w, pb, false) : WSt) := by
      simp only [StoreSt.wst, StoreSt.wreturn, ← hwv, ← hwtx, ← hpb]
    rw [ew]
    iframe
    ipureintro
    exact storeOK_wreturn σ Hok
  imodintro; iframe

/-- The remap: the parked view re-borrowed on the new mapping's base. -/
theorem store_wborrow (v : View) (w : Option Nat) (pb : Bool) (b : Loc) (l : Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗
      ghostVar B.wv (1 : Qp).half ((some v, w, pb, false) : WSt) ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ⊢
    |={E}=> ghostVar B.wv (1 : Qp).half ((some { v with base := b }, w, pb, true) : WSt) ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      viewCells wq { v with base := b } := by
  iintro ⟨#Hinv, Hwv, Hmap⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  simp only [StoreSt.wst, Prod.mk.injEq] at hws
  obtain ⟨hwv, hwtx, hpb, hwl⟩ := hws
  have hms' : σ.ms = some (b, l) := hms.symm
  icases sep_keep_pure (deposits_le _ B.mtok sync.rfrac σ.R) $$ Hdep with ⟨Hdep, %Hsz⟩
  have hok' := storeOK_wborrow_some σ v b l Hok hwv.symm hms'
  have hwok := hok'.2.2.2.2.2.2.2.1 { v with base := b } (by simp [StoreSt.wborrow, ← hwv])
  obtain ⟨hTn, hTs, hTl⟩ := view_slots (σ.wborrow b) hok' _ hwok.2.2.1 hwok.2.2.2.1
  imod ghostVar_update_halves ((some { v with base := b }, w, pb, true) : WSt) B.wv _ _ $$ Hwv Hwv'
    with ⟨Hwv, Hwv'⟩
  rw [storeCells_some σ b l hms']
  icases cells_borrow (storeSlots σ) (pagesSlots v.pages) (nodup_list_dedup _) hTn hTs
    (slotPt b σ.bytes) (slotPt_add b σ.bytes) (lent σ) (lent (σ.wborrow b)) wq (1 : Qp).half
    (fun s _ => by
      unfold lent; rw [← hwl]
      simp only [StoreSt.wborrow, ← hwv, Option.map_some]
      by_cases hc : coversSlot v.pages s
      · simp [hc, (mem_pagesSlots _ _).2 hc]
      · simp [hc, show s ∉ pagesSlots v.pages from fun h => hc ((mem_pagesSlots _ _).1 h)])
    (fun s _ x hx => lent_lt_half2 (σ.wborrow b) Hsz s x hx)
    $$ Hcells with ⟨Hcells, Hv⟩
  ihave Hv := (viewCells_slots wq { v with base := b } σ.bytes hwok.2.2.2.2.1 hTl).2 $$ Hv
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.wborrow b, W
    rw [storeCells_some (σ.wborrow b) b l hms']
    have e2 : metaLend (GF := GF) B (σ.wborrow b) = metaLend B σ := rfl
    have e3 : bytesWit (GF := GF) B (σ.wborrow b) W = bytesWit B σ W := rfl
    rw [e2, e3]
    have ew : (σ.wborrow b).wst = ((some { v with base := b }, w, pb, true) : WSt) := by
      simp only [StoreSt.wst, StoreSt.wborrow, ← hwv, ← hwtx, ← hpb, Option.map_some]
    rw [ew]
    iframe
    ipureintro
    exact hok'
  imodintro; iframe

/-- The writer's `close` (any path): its view returned (if lent), no live writer; published, or
nothing pending for it. -/
theorem store_wclose (v : View) (w : Nat) (pb wl : Bool) (fl : FLPg)
    (hp : pb = true ∨ fl.pending !! W64 (w : Int) = none) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗
      ghostVar B.wv (1 : Qp).half ((some v, some w, pb, wl) : WSt) ∗
      (if wl then viewCells wq v else iprop(emp)) ∗ ghostVar B.fl (1 : Qp).half fl ⊢
    |={E}=> ghostVar B.wv (1 : Qp).half wIdle ∗ ghostVar B.fl (1 : Qp).half fl := by
  sorry

/-- `Free(w, p)` of `n` slots from `id` by the live writer before its publish: a page of the
current tree, or the old synced freelist page, whose slots then move `W → store` (F4.5). -/
theorem store_free (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) (w : Nat) (id : w64)
    (n : Nat) (pg : Nat → List w8) (hw : ws.2.1 = some w) (hpub : ws.2.2.1 = false)
    (hcan : fl.canFree (W64 (w : Int)) id n) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ws ∗
      ((⌜∃ q, C.pages !! id.toNat = some q ∧ 1 + pageOverflow q = n⌝) ∨
        (⌜C.flpg = some id.toNat ∧ ms ≠ none ∧ id.toNat + n ≤ C.hwm ∧
          ∀ j < n, (pg (id.toNat + j)).length = 4096 ∧
          ∀ b l, ms = some (b, l) → id.toNat + j < l / 4096⌝ ∗
          slotsOwn ms p (List.range' id.toNat n) pg)) ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half (fl.freePages (W64 (w : Int)) id n) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws := by
  sorry

/-- `Allocate` by the live writer: the ids leave the free list (their slots are `W` slots
already). -/
theorem store_alloc (fl : FLPg) (ws : WSt) (w : Nat) (r : w64) (n : Nat)
    (hw : ws.2.1 = some w) (ha : fl.canAlloc r n) (hn : 0 < n) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ghostVar B.fl (1 : Qp).half (fl.alloc (W64 (w : Int)) r n) ∗
      ghostVar B.wv (1 : Qp).half ws := by
  sorry

/-- `ReleasePendingPages` with no live writer, under `metalock` (`metaR`'s `F`, whose values are
`readonlyTXIDs` `ro`): the released slots move `store → W`, with their cells and bytes. -/
theorem store_release (C : CommitSt) (fl : FLPg) (ms : MapSt) (F : GMap Nat w64)
    (ro : List w64) (hro : ro.Perm (F.toList.map Prod.snd))
    (hro1 : ∀ k t, F !! k = some t → 1 ≤ t.toNat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half wIdle ∗ ghostMapAuth B.fltx 1 F ⊢
    |={E}=> ∃ (S : List Nat) (bs : Nat → List w8),
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half (fl.releasePending ro) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half wIdle ∗
      ghostMapAuth B.fltx 1 F ∗ slotsOwn ms p S bs ∗
      ⌜∀ s, s ∈ S ↔ s ∈ slotsOf C fl ∧ s ∉ slotsOf C (fl.releasePending ro)⌝ := by
  sorry

/-- **The commit point** (U10): the committed state moves `C → C'` (with `metaR`'s half and the
writer's quarter of `cur`), the new tree's slots `S` move `W → store` with their bytes; the
writer has published. The side conditions are spill's post (design §4.2). -/
theorem store_publish (C C' : CommitSt) (fl : FLPg) (ms : MapSt) (v : View) (w : Nat)
    (wl : Bool) (S : List Nat) (bs : Nat → List w8)
    (ht : C'.txid = w) (hmeta : C'.metaOk) (htree : treeOK C') (hhwm : C'.hwm ≤ 2 ^ 62)
    (hdrop : ∀ s ∈ treeSlots C, s ∉ treeSlots C' → s ∈ pendSlots fl)
    (hS : ∀ s, s ∈ S ↔ s ∈ treeSlots C' ∧ s ∉ slotsOf C fl)
    (hbytes : ∀ id pg, C'.pages !! id = some pg → C.pages !! id = some pg ∨
      ((∀ j < 1 + pageOverflow pg, id + j ∈ S) ∧
        pg = (List.range' id (1 + pageOverflow pg)).flatMap bs))
    (hfl : flBelow fl C' (some w)) (hnp : ∀ s ∈ treeSlots C', s ∉ pendSlots fl)
    (hSb : ∀ s ∈ S, (bs s).length = 4096 ∧ W64 (s : Int) ∉ fl.free ∧
      ∀ b l, ms = some (b, l) → s < l / 4096) (hms : ms ≠ none) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ((some v, some w, false, wl) : WSt) ∗ slotsOwn ms p S bs ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half C' ∗ ghostVar B.cur (1 : Qp).half.half C' ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ((some v, some w, true, wl) : WSt) := by
  sorry

/-- `freelist.Rollback(w)` by the live writer before its publish: `w`'s pending pages are not
pending; slots leaving the store (B3: a freed old synced freelist page) move `store → W`. -/
theorem store_rollback (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) (w : Nat)
    (hw : ws.2.1 = some w) (hpub : ws.2.2.1 = false) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ∃ (S : List Nat) (bs : Nat → List w8),
      ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half (fl.rollback (W64 (w : Int))) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ∗ slotsOwn ms p S bs ∗
      ⌜∀ s, s ∈ S ↔ s ∈ slotsOf C fl ∧ s ∉ slotsOf C (fl.rollback (W64 (w : Int)))⌝ := by
  sorry

/-- `Reload`/`NoSyncReload`: the free ids rebuilt from `W` slots below the high-water mark. -/
theorem store_reload (C : CommitSt) (fl : FLPg) (ids : List w64)
    (hids : ∀ x ∈ ids, 2 ≤ x.toNat ∧ x.toNat < C.hwm ∧ x.toNat < 2 ^ 62 ∧
      (x.toNat ∉ slotsOf C fl ∨ x ∈ fl.pendingIds)) (hnd : ids.Nodup) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half (fl.reload ids) := by
  iintro ⟨#Hinv, Hcur, Hfl⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv, Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  subst hC hfl
  imod ghostVar_update_halves (σ.fl.reload ids) B.fl σ.fl σ.fl $$ Hfl Hfl' with ⟨Hfl, Hfl'⟩
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv Hrds Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists (σ.reload ids), W
    have e1 : storeCells (GF := GF) (σ.reload ids) = storeCells σ := rfl
    have e2 : metaLend (GF := GF) B (σ.reload ids) = metaLend B σ := rfl
    have e3 : bytesWit (GF := GF) B (σ.reload ids) W = bytesWit B σ W := rfl
    rw [e1, e2, e3]
    iframe
    ipureintro
    exact storeOK_reload σ ids Hok hids hnd
  imodintro; iframe

/-- `munmap` (a remap, `Close`), with `Pm 1` (`mtok 1`, its `map` quarter) and the writer's view
parked: every store cell comes out at the client half, and the meta lend quarter. -/
theorem store_gather (C : CommitSt) (fl : FLPg) (b : Loc) (l : Nat) (ws : WSt)
    (hwl : ws.2.2.2 = false) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (some (b, l) : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half ws ∗ ghostVar B.out (1 : Qp).half false ⊢
    |={E}=> ∃ (bs : Nat → List w8) (W : GMap Nat (List w8)),
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half (none : MapSt) ∗ ghostVar B.map (1 : Qp).half.half (none : MapSt) ∗
      ghostVar B.mtok 1 () ∗ ghostVar B.wv (1 : Qp).half ws ∗ ghostVar B.out (1 : Qp).half false ∗
      ghostVar B.byt (1 : Qp).half W ∗ ⌜∀ s ∈ slotsOf C fl, W !! s = some (bs s)⌝ ∗
      ([∗list] s ∈ slotsOf C fl,
        bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s)) ∗
      metaCellsQ (1 : Qp).half.half (some (b, l)) C := by
  sorry

/-- `mmap` (a remap): the new mapping's store cells in, holding the page cache's bytes (the
caller read them with OsFs's `osCell_agree`), and the meta lend quarter. -/
theorem store_carve (C : CommitSt) (fl : FLPg) (b : Loc) (l : Nat) (ws : WSt)
    (bs : Nat → List w8) (W : GMap Nat (List w8)) (hl : ∀ s ∈ slotsOf C fl, s < l / 4096)
    (hW : ∀ s ∈ slotsOf C fl, W !! s = some (bs s)) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half (none : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (none : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half ws ∗ ghostVar B.byt (1 : Qp).half W ∗
      ([∗list] s ∈ slotsOf C fl,
        bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s)) ∗
      metaCellsQ (1 : Qp).half.half (some (b, l)) C ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (some (b, l) : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half ws := by
  sorry

/-- `beginTx`'s `t.init` under `metalock` and `Pm rfrac`: the reader deposits `mlk` and
`mtok (rfrac/2)` and borrows the meta cells' quarter. -/
theorem meta_borrow (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.mlk 1 () ∗
      ghostVar B.mtok sync.rfrac.half () ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half ms ⊢
    |={E}=> metaCellsQ (1 : Qp).half.half ms C ∗ ghostVar B.mln 1 () ∗
      ghostVar B.cur (1 : Qp).half C ∗ ghostVar B.map sync.rfrac.half.half ms := by
  sorry

/-- The reader gives the meta cells' quarter back and gets its deposits. -/
theorem meta_return (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ metaCellsQ (1 : Qp).half.half ms C ∗
      ghostVar B.mln 1 () ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half ms ⊢
    |={E}=> ghostVar B.mlk 1 () ∗ ghostVar B.mtok sync.rfrac.half () ∗
      ghostVar B.cur (1 : Qp).half C ∗ ghostVar B.map sync.rfrac.half.half ms := by
  sorry

/-- `writeMeta`, holding `metalock` (`mlk`): the writer takes the meta cells' quarter
(`out := true`), depositing `mlk` until it puts them back. -/
theorem meta_take (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.out (1 : Qp).half false ∗
      ghostVar B.mlk 1 () ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half ms ⊢
    |={E}=> metaCellsQ (1 : Qp).half.half ms C ∗ ghostVar B.out (1 : Qp).half true ∗
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.map (1 : Qp).half ms := by
  iintro ⟨#Hinv, Hout, Hmlk, Hcur, Hmap⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl, Hmap', Hwv, Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  subst hC hms
  unfold metaLend
  icases Hml with (⟨Hm, Hout', Hln⟩ | ⟨Hout', -, -⟩ | ⟨Hout', Hmlk', -⟩)
  · imod ghostVar_update_halves true B.out false false $$ Hout Hout' with ⟨Hout, Hout'⟩
    imod Hclose $$ [Hcur' Hfl Hmap' Hwv Hrds Hdep Hcells Hos Hbw Hout' Hmlk Hln] with _
    · inext; iexists σ, W; iframe
      isplitl [Hout' Hmlk Hln]
      · iright; ileft; iframe
      ipureintro; exact Hok
    imodintro; iframe
  · icombine Hout Hout' gives % ⟨_, hb⟩; cases hb
  · icombine Hmlk Hmlk' gives % ⟨hq, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    grind

/-- The writer puts the meta cells' quarter back, holding the current committed state's metas
(after `store_publish`, or unchanged), and gets `mlk` back. -/
theorem meta_put (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.out (1 : Qp).half true ∗
      metaCellsQ (1 : Qp).half.half ms C ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half ms ⊢
    |={E}=> ghostVar B.out (1 : Qp).half false ∗ ghostVar B.mlk 1 () ∗
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.map (1 : Qp).half ms := by
  iintro ⟨#Hinv, Hout, Hm, Hcur, Hmap⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl, Hmap', Hwv, Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  subst hC hms
  unfold metaLend
  icases Hml with (⟨-, Hout', -⟩ | ⟨Hout', Hmlk, Hln⟩ | ⟨Hout', -, -⟩)
  · icombine Hout Hout' gives % ⟨_, hb⟩; cases hb
  · imod ghostVar_update_halves false B.out true true $$ Hout Hout' with ⟨Hout, Hout'⟩
    imod Hclose $$ [Hcur' Hfl Hmap' Hwv Hrds Hdep Hcells Hos Hbw Hout' Hm Hln] with _
    · inext; iexists σ, W; iframe
      isplitl [Hout' Hm Hln]
      · ileft; iframe
      ipureintro; exact Hok
    imodintro; iframe
  · icombine Hout Hout' gives % ⟨_, hb⟩; cases hb

end lemmas

end store

end bbolt
end EtcdGrove
end Perennial
