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

open Fs

open Iris Iris.BI go_etcd_io.bbolt

section fbrec
-- pure (no instances), so that pure modules can use `fbRec_lookup`

/-- The bytes `pg` of the run of `n` slots from `id`, recorded (`store_free_fl`'s `fpb` value). -/
def fbRec (id : w64) (n : Nat) (pg : Nat → List w8) : GMap Nat (List w8) :=
  (List.range' id.toNat n).foldr (fun s m => m.insert s (pg s)) ∅

theorem fbRec_lookup (id : w64) (n : Nat) (pg : Nat → List w8) (s : Nat) :
    fbRec id n pg !! s = if s ∈ List.range' id.toNat n then some (pg s) else none := by
  unfold fbRec
  induction List.range' id.toNat n with
  | nil => simp
  | cons a S ih =>
    simp only [List.foldr_cons, GMap.lookup_insert_eq_iff] at ih ⊢
    by_cases h : a = s
    · subst h; simp
    · rw [if_neg h, ih]; simp [Ne.symm h]

end fbrec

section store
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The store slots of a committed state and a freelist (`storeSlots σ = slotsOf σ.C σ.fl`). -/
def slotsOf (C : CommitSt) (fl : FLPg) : List Nat := listDedup (treeSlots C ++ pendSlots fl)

/-- A view's cells at the fraction `q`: page `id` at `base + 4096 · id`. -/
def viewCells (q : Qp) (v : View) : IProp GF :=
  iprop([∗map] id ↦ pg ∈ v.pages, bytesPointsto (v.base +ₗ ((id * 4096 : Nat) : Int)) (DFrac.own q) pg)

/-- The page-cache bytes of slot `s` of the file `p`, all of them, holding `bs`. -/
def osSlot (p : BFile) (s : Nat) (bs : List w8) : IProp GF :=
  iprop(∃ xs : List ByteG, osBytes p.ino (4096 * s) (DFrac.own 1) xs ∗ ⌜xs.map Prod.fst = bs⌝)

/-- The slots `S` whole, as they move between the store and `W`: their client cell halves (when
mapped) and their page-cache bytes, holding `bs`. -/
def slotsOwn (ms : MapSt) (p : BFile) (S : List Nat) (bs : Nat → List w8) : IProp GF :=
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

/-- **The live writer has freed the synced freelist page and not published** (batch 40B):
`C`'s freelist page `f` (no tree slot) is in the pending entry of the writer `w` (`wtx`), before
its publish (`pb`). Only `Commit`'s `commitFreelist` frees it (`store_free_fl`); a rollback
(`store_rollback`), the publish (`store_publish`) end it. -/
def fbCond (C : CommitSt) (fl : FLPg) (wtx : Option Nat) (pb : Bool) : Prop :=
  pb = false ∧ ∃ w f pd, wtx = some w ∧ C.flpg = some f ∧ ¬ coversSlot C.pages f ∧
    fl.pending !! W64 (w : Int) = some pd ∧ ∃ x ∈ pd.ids, x.toNat = f

/-- **The freed freelist page's bytes** (batch 40B, ghost name `fpb`): half here; the other half
here too, or (only while `fbCond`) with the writer, which took it at the page's free; while
`fbCond`, the store slots recorded in `F` hold the recorded bytes (the bytes the writer deposited
with the page's slots), so that `store_rollback` returns them. -/
def fbInv (B : BNs) (σ : StoreSt) : IProp GF :=
  iprop(∃ F : GMap Nat (List w8), ghostVar B.fpb (1 : Qp).half F ∗
    (ghostVar B.fpb (1 : Qp).half F ∨ ⌜fbCond σ.C σ.fl σ.wtx σ.pub⌝) ∗
    ⌜fbCond σ.C σ.fl σ.wtx σ.pub → ∀ s v, F !! s = some v → s ∈ storeSlots σ → σ.bytes s = v⌝)

/-- **The writer's side of `fbInv`** (batch 40B) for the store's state `C`, `fl`, `ws`: the
recorded bytes `F`' half when the writer has freed the synced freelist page (`fbCond`), nothing
otherwise. -/
def fbTok (B : BNs) (C : CommitSt) (fl : FLPg) (ws : WSt) (F : GMap Nat (List w8)) : IProp GF :=
  iprop((⌜fbCond C fl ws.2.1 ws.2.2.1⌝ ∗ ghostVar B.fpb (1 : Qp).half F) ∨
    ⌜¬ fbCond C fl ws.2.1 ws.2.2.1⌝)

omit go_gctx sem in
instance fbInv_timeless (B : BNs) (σ : StoreSt) : Timeless (fbInv (GF := GF) B σ) := by
  unfold fbInv; infer_instance

omit go_gctx sem in
/-- **No freed freelist page under `wdbOK`** (batch 40B): `flCurOK` keeps the synced freelist
page's slots out of the freelist, so `fbCond` fails: a writer side with `wdbOK` holds `fbTok` with
nothing (`fbTok_of_wdbOK`). -/
theorem wdbOK_not_fbCond (w : WDb) (hok : wdbOK w) (wtx : Option Nat) (pb : Bool) :
    ¬ fbCond w.C w.fl wtx pb := by
  rintro ⟨-, t, f, pd, -, hf, -, hp, x, hx, hxf⟩
  obtain ⟨-, -, -, -, -, -, -, -, hsl, -⟩ := hok.2.2.2.2.2.1 f hf f hf
  apply (hsl f (Nat.le_refl _) (by omega)).2
  have hx' : W64 (f : Int) = x := by
    rw [← hxf]; simp only [W64, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hx']
  simp only [FLPg.allIds, FLPg.pendingIds, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(W64 (t : Int), pd), (GMap.mem_toList _ _ _).2 hp, hx⟩

omit go_gctx sem in
theorem fbTok_of_wdbOK (B : BNs) (w : WDb) (hok : wdbOK w) (ws : WSt) (F : GMap Nat (List w8)) :
    ⊢ fbTok (GF := GF) B w.C w.fl ws F := by
  unfold fbTok; iright; ipureintro; exact wdbOK_not_fbCond w hok _ _

/-- **The store slots' bytes, as a ghost witness** `W` (U3 finding 11): half here, the other half
here too while mapped (`store_gather` hands it out with the cells, `store_carve` takes both
back, so that the new mapping's cells are known to hold the store's bytes); and the freed freelist
page's recorded bytes (`fbInv`, batch 40B). -/
def bytesWit (B : BNs) (σ : StoreSt) (W : GMap Nat (List w8)) : IProp GF :=
  iprop(ghostVar B.byt (1 : Qp).half W ∗
    (match σ.ms with
     | some _ => ghostVar B.byt (1 : Qp).half W
     | none => iprop(emp)) ∗
    ⌜∀ s ∈ storeSlots σ, W !! s = some (σ.bytes s)⌝ ∗ fbInv B σ)

/-- The registered readers `R` (auth) with `pagesInv`'s quarter of the spare state `B.spr` and,
unless the opening is over, the spare clause (batch 41). -/
def rdsAuth (B : BNs) (R : GMap Nat RdInfo) : IProp GF :=
  iprop(ghostMapAuth B.rds 1 R ∗ ∃ o : Option Nat, ghostVar B.spr (1 : Qp).half.half o ∗
    (opnShot B ∨ ⌜sprCl o R⌝))

omit go_gctx sem in
instance rdsAuth_timeless (B : BNs) (R : GMap Nat RdInfo) : Timeless (rdsAuth (GF := GF) B R) := by
  unfold rdsAuth opnShot; infer_instance

/-- **The page store's invariant** (design §3.6). -/
def pagesInv (B : BNs) (p : BFile) : IProp GF :=
  iprop(∃ (σ : StoreSt) (W : GMap Nat (List w8)),
    ghostVar B.cur (1 : Qp).half.half σ.C ∗ ghostVar B.fl (1 : Qp).half σ.fl ∗
    ghostVar B.map (1 : Qp).half.half σ.ms ∗ ghostVar B.wv (1 : Qp).half σ.wst ∗
    rdsAuth B σ.R ∗
    ([∗map] k ↦ r ∈ σ.R, k ↪[B.fltx] (W64 (r.v.txid : Int)) ∗ ghostVar B.mtok sync.rfrac ()) ∗
    storeCells σ ∗ ([∗list] s ∈ storeSlots σ, osSlot p s (σ.bytes s)) ∗ bytesWit B σ W ∗
    metaLend B σ ∗ ⌜storeOK σ⌝)

/-! ## Lemma statements (U3), fancy updates at `pagesN N` -/

omit go_gctx sem in
private theorem pagesInv_timeless (B : BNs) (p : BFile) : Timeless (pagesInv (GF := GF) B p) := by
  have h1 : ∀ σ : StoreSt, Timeless (storeCells (GF := GF) σ) := by
    intro σ; unfold storeCells; split <;> infer_instance
  have h2 : ∀ σ : StoreSt, Timeless (metaLend (GF := GF) B σ) := by
    intro σ; unfold metaLend metaCellsQ; split <;> infer_instance
  have h4 : ∀ σ W, Timeless (bytesWit (GF := GF) B σ W) := by
    intro σ W; unfold bytesWit; split <;> infer_instance
  have h3 : ∀ s bs, Timeless (osSlot (GF := GF) p s bs) := by
    intro s bs
    have : ∀ off dq xs, Timeless (osBytes (GF := GF) p.ino off dq xs) := fun _ _ _ => by
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

omit go_gctx sem in
/-- Three halves of `fpb` are absurd. -/
private theorem fpb_three (B : BNs) (a b c : GMap Nat (List w8)) :
    ghostVar (GF := GF) B.fpb (1 : Qp).half a ∗ ghostVar B.fpb (1 : Qp).half b ∗
      ghostVar B.fpb (1 : Qp).half c ⊢ ⌜False⌝ := by
  iintro ⟨H1, H2, H3⟩
  icombine H1 H2 gives % ⟨_, h⟩
  subst h
  ihave H12 := ((ghostVar_fractional (GF := GF) B.fpb a).fractional (1 : Qp).half
    (1 : Qp).half).2 $$ [H1 H2]
  · iframe
  ihave %hv := ghostVar_valid_2 B.fpb a ((1 : Qp).half + (1 : Qp).half) c (1 : Qp).half $$ H12 H3
  ipureintro
  have h := hv.1
  rw [Qp.le_iff] at h
  simp only [Qp.val_add, Qp.val_half, Qp.val_one] at h
  grind

omit go_gctx sem in
/-- `bytesWit` across a step that keeps the mapping, the store slots and their bytes, with no
freed freelist page before or after (`fbCond`): the `fpb` token is home throughout. -/
private theorem bytesWit_nocond (B : BNs) (σ σ' : StoreSt) (W : GMap Nat (List w8))
    (hms : σ'.ms = σ.ms) (hss : storeSlots σ' = storeSlots σ) (hb : σ'.bytes = σ.bytes)
    (h1 : ¬ fbCond σ.C σ.fl σ.wtx σ.pub) (h2 : ¬ fbCond σ'.C σ'.fl σ'.wtx σ'.pub) :
    bytesWit (GF := GF) B σ W ⊢ bytesWit B σ' W := by
  unfold bytesWit fbInv
  rw [hms, hss, hb]
  iintro ⟨Hb1, Hb2, %hW, %F, Hf1, Hf2, -⟩
  icases Hf2 with (Hf2 | %hc)
  · isplitl [Hb1]
    · iexact Hb1
    isplitl [Hb2]
    · iexact Hb2
    isplitr
    · ipureintro; exact hW
    iexists F
    isplitl [Hf1]
    · iexact Hf1
    isplitl [Hf2]
    · ileft; iexact Hf2
    ipureintro; intro hc; exact absurd hc h2
  · exact absurd hc h1

omit go_gctx sem in
/-- **The writer's `fpb` half back** (batch 40B) at a step ending `fbCond` (a rollback, the
publish): with the writer's `fbTok`, the token is home after; while `fbCond` held, the recorded
bytes were the store's. -/
private theorem fbInv_return (B : BNs) (σ σ' : StoreSt) (ws : WSt) (F : GMap Nat (List w8))
    (hw : ws.2.1 = σ.wtx) (hp : ws.2.2.1 = σ.pub)
    (h2 : ¬ fbCond σ'.C σ'.fl σ'.wtx σ'.pub) :
    fbInv (GF := GF) B σ ∗ fbTok B σ.C σ.fl ws F ⊢
      fbInv B σ' ∗ ⌜fbCond σ.C σ.fl σ.wtx σ.pub →
        ∀ s v, F !! s = some v → s ∈ storeSlots σ → σ.bytes s = v⌝ := by
  unfold fbInv fbTok
  rw [hw, hp]
  iintro ⟨⟨%F0, Hf1, Hf2, %hok⟩, Ht⟩
  icases Ht with (⟨%hc, Ht⟩ | %hnc)
  · icases Hf2 with (Hf2 | %-)
    · icases fpb_three B F F0 F0 $$ [Ht Hf1 Hf2] with %hf
      · iframe
      exact hf.elim
    icombine Ht Hf1 gives % ⟨_, hF⟩
    subst hF
    isplitl [Ht Hf1]
    · iexists F
      isplitl [Hf1]
      · iexact Hf1
      isplitl [Ht]
      · ileft; iexact Ht
      ipureintro; intro hc'; exact absurd hc' h2
    ipureintro; intro _; exact hok hc
  · icases Hf2 with (Hf2 | %hc)
    · isplitl [Hf1 Hf2]
      · iexists F0
        isplitl [Hf1]
        · iexact Hf1
        isplitl [Hf2]
        · ileft; iexact Hf2
        ipureintro; intro hc'; exact absurd hc' h2
      ipureintro; intro hc; exact absurd hc hnc
    · exact absurd hc hnc

/-- The spare state `B.spr`'s three shares (spare side ½, `metaR`'s and `pagesInv`'s quarters)
agree and are set together (batch 41). -/
private theorem spr_update (B : BNs) (E : CoPset) (o' : Option Nat) {o1 o2 o3 : Option Nat} :
    ghostVar (GF := GF) B.spr (1 : Qp).half o1 ∗ ghostVar B.spr (1 : Qp).half.half o2 ∗
      ghostVar B.spr (1 : Qp).half.half o3 ⊢
    |={E}=> ghostVar B.spr (1 : Qp).half o' ∗ ghostVar B.spr (1 : Qp).half.half o' ∗
      ghostVar B.spr (1 : Qp).half.half o' ∗ ⌜o2 = o1 ∧ o3 = o1⌝ := by
  iintro ⟨H1, H2, H3⟩
  icombine H1 H2 gives % ⟨_, h12⟩
  icombine H1 H3 gives % ⟨_, h13⟩
  subst h12 h13
  ihave H23 := ((ghostVar_fractional (GF := GF) B.spr o1).fractional (1 : Qp).half.half
    (1 : Qp).half.half).2 $$ [H2 H3]
  · iframe
  imod ghostVar_update_2 o' B.spr o1 (1 : Qp).half o1 ((1 : Qp).half.half + (1 : Qp).half.half)
    (by rw [Qp.half_add_half, Qp.half_add_half]) $$ H1 H23 with ⟨H1, H23⟩
  ihave ⟨H2, H3⟩ := ((ghostVar_fractional (GF := GF) B.spr o').fractional (1 : Qp).half.half
    (1 : Qp).half.half).1 $$ H23
  imodintro
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  isplitl [H3]
  · iexact H3
  ipureintro; exact ⟨rfl, rfl⟩

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

private theorem lent_wclose (σ : StoreSt) (hwl : σ.wlent = false) : lent σ.wclose = lent σ := by
  funext s
  unfold lent
  simp only [StoreSt.wclose]
  split <;> simp_all

private theorem register_deregister (σ : StoreSt) (k : Nat) (r : RdInfo) (hk : σ.R !! k = none) :
    (σ.register k r).deregister k = σ := by
  simp only [StoreSt.deregister, StoreSt.register, GMap.delete_insert _ _ _ hk]

private theorem lent_register (σ : StoreSt) (k : Nat) (r : RdInfo) (hk : σ.R !! k = none) (s : Nat) :
    lent (σ.register k r) s = if s ∈ pagesSlots r.v.pages then optAdd rq (lent σ s)
      else lent σ s := by
  have := lent_deregister (σ.register k r) k r (by simp [StoreSt.register]) s
  rwa [register_deregister σ k r hk] at this

open Classical in
private theorem lent_wbegin (σ : StoreSt) (v : View) (hwv : σ.wv = none) (s : Nat) :
    lent (σ.wbegin v) s = if s ∈ pagesSlots v.pages then optAdd wq (lent σ s) else lent σ s := by
  unfold lent
  simp only [StoreSt.wbegin, hwv]
  by_cases hc : coversSlot v.pages s
  · simp [hc, (mem_pagesSlots _ _).2 hc]
  · simp [hc, show s ∉ pagesSlots v.pages from fun h => hc ((mem_pagesSlots _ _).1 h)]


open Classical in
private theorem lent_none (σ : StoreSt) (hR : σ.R = ∅) (hwl : σ.wlent = false) (s : Nat) :
    lent σ s = none := by
  unfold lent
  rw [hR, GMap.mapFold_empty]
  split <;> simp_all

private theorem cells_unlent (S : List Nat) (A : Nat → Qp → IProp GF) (L : Nat → Option Qp)
    (hL : ∀ s ∈ S, L s = none) :
    ([∗list] s ∈ S, ∃ e, ⌜fracSum e (L s) (1 : Qp).half⌝ ∗ A s e) ⊣⊢
      [∗list] s ∈ S, A s (1 : Qp).half := by
  constructor
  · refine bigSepL_mono_mem fun s hs => ?_
    iintro ⟨%e, %he, H⟩
    rw [hL s hs] at he; simp only [fracSum] at he; subst he; iexact H
  · refine bigSepL_mono_mem fun s hs => ?_
    iintro H
    iexists (1 : Qp).half
    isplitr
    · ipureintro; rw [hL s hs]; rfl
    · iexact H

private theorem R_empty_of_tok (B : BNs) (R : GMap Nat RdInfo) :
    ([∗map] k ↦ r ∈ R, k ↪[B.fltx] (W64 (r.v.txid : Int)) ∗ ghostVar B.mtok sync.rfrac ()) ∗
      ghostVar (GF := GF) B.mtok 1 () ⊢
    (([∗map] k ↦ r ∈ R, k ↪[B.fltx] (W64 (r.v.txid : Int)) ∗ ghostVar B.mtok sync.rfrac ()) ∗
      ghostVar (GF := GF) B.mtok 1 ()) ∗ ⌜R = ∅⌝ := by
  refine sep_keep_pure ?_
  refine (deposits_le_aux (fun k' (r' : RdInfo) => iprop(k' ↪[B.fltx] (W64 (r'.v.txid : Int))))
    B.mtok sync.rfrac R 1).trans (pure_mono fun h => ?_)
  have hpos := sync.rfrac.2
  simp only [Qp.val_one] at h
  have : (R.size : Rat) * sync.rfrac.val = 0 := by
    have : (0 : Rat) ≤ (R.size : Rat) * sync.rfrac.val :=
      Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (Rat.le_of_lt hpos)
    grind
  have hsz : R.size = 0 := by
    rcases Nat.eq_zero_or_pos R.size with h0 | h0
    · exact h0
    · exfalso
      have : (0 : Rat) < (R.size : Rat) * sync.rfrac.val :=
        Rat.mul_pos (by exact_mod_cast h0) hpos
      grind
  exact GMap.map_size_empty_inv R hsz

private theorem W64_toNat_of_lt' (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

/-- No freed freelist page right after the writer's begin: no pending entry of the next txid
(`flBelow`, no writer before). -/
private theorem fbCond_wbegin (σ : StoreSt) (h : storeOK σ) (hw : σ.wtx = none) :
    ¬ fbCond σ.C σ.fl (some (σ.C.txid + 1)) false := by
  rintro ⟨-, w, f, pd, hw', -, -, hp, -⟩
  cases hw'
  have hfb := h.2.2.1
  have hlt : σ.C.txid + 1 < 2 ^ 64 := hfb.2.2.2.1
  rcases hfb.2.2.1 _ pd hp with h1 | ⟨h1, -⟩
  · rw [W64_toNat_of_lt' _ hlt] at h1; omega
  · rw [hw] at h1; cases h1

/-- No freed freelist page without a live writer. -/
private theorem fbCond_none (C : CommitSt) (fl : FLPg) (pb : Bool) : ¬ fbCond C fl none pb := by
  rintro ⟨-, w, f, pd, hw', -⟩; cases hw'

private theorem W64_toNat_eq (x : w64) : W64 (x.toNat : Int) = x := by
  simp only [W64, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem mem_pagesSlots' (P : Pages) (s : Nat) : s ∈ pagesSlots P ↔ coversSlot P s := by
  simp only [pagesSlots, List.mem_flatMap, List.mem_range', coversSlot]
  constructor
  · rintro ⟨⟨id, pg⟩, hip, j, hj, rfl⟩
    exact ⟨id, pg, (GMap.mem_toList _ _ _).1 hip, by omega, by simp only at hj; omega⟩
  · rintro ⟨id, pg, hp, h1, h2⟩
    exact ⟨(id, pg), (GMap.mem_toList _ _ _).2 hp, s - id, by simp only; omega, by omega⟩

private theorem tree_in_store' (σ : StoreSt) (s : Nat) (h : coversSlot σ.C.pages s) :
    s ∈ storeSlots σ := by
  simp only [storeSlots, mem_list_dedup, List.mem_append]
  exact Or.inl ((mem_pagesSlots' _ _).2 h)

private theorem treeSlot_lt64 (σ : StoreSt) (h : storeOK σ) (s : Nat) (hs : coversSlot σ.C.pages s) :
    s < 2 ^ 64 := by
  obtain ⟨id, pg, hp, h1, h2⟩ := hs
  have := h.2.1.2.2.2.1 id pg hp
  have hm := h.1.2.2.2.2.2.2.1.2.2.1
  have := (metaOf (σ.C.slot σ.C.txid)).pgid'.isLt
  omega

private theorem mem_pendSlots (fl : FLPg) (s : Nat) :
    s ∈ pendSlots fl ↔ ∃ t pd x, fl.pending !! t = some pd ∧ x ∈ pd.ids ∧ x.toNat = s := by
  simp only [pendSlots, FLPg.pendingIds, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨⟨t, pd⟩, hkv, hx⟩, rfl⟩
    exact ⟨t, pd, x, (GMap.mem_toList _ _ _).1 hkv, hx, rfl⟩
  · rintro ⟨t, pd, x, hp, hx, rfl⟩
    exact ⟨x, ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩, rfl⟩

private theorem run_toNat (id : w64) (n j : Nat) (hj : j < n) (hn : id.toNat + n < 2 ^ 64) :
    (id + W64 (j : Int)).toNat = id.toNat + j := by
  simp only [W64, BitVec.toNat_add, BitVec.toNat_ofInt]; omega

private theorem mem_runIds' (id : w64) (n : Nat) (x : w64) :
    x ∈ runIds id n ↔ ∃ j < n, x = id + W64 (j : Int) := by
  simp only [runIds, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

private theorem mem_runIds_toNat (id : w64) (n : Nat) (hn : id.toNat + n < 2 ^ 64) (x : w64) :
    x ∈ runIds id n ↔ id.toNat ≤ x.toNat ∧ x.toNat < id.toNat + n := by
  rw [mem_runIds']
  constructor
  · rintro ⟨j, hj, rfl⟩; rw [run_toNat id n j hj hn]; omega
  · intro ⟨h1, h2⟩
    refine ⟨x.toNat - id.toNat, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [run_toNat id n _ (by omega) hn]; omega

private theorem inRun_W64 (id : w64) (n s : Nat) (hs : s < 2 ^ 64) :
    inRun id n (W64 (s : Int)) ↔ id.toNat ≤ s ∧ s < id.toNat + n := by
  unfold inRun; rw [W64_toNat_of_lt' s hs]

private theorem freePages_lookup (fl : FLPg) (T id : w64) (n : Nat) (t : w64) (pd : Pending)
    (h : (fl.freePages T id n).pending !! t = some pd) :
    (t ≠ T ∧ fl.pending !! t = some pd) ∨
    (t = T ∧ ∃ P : Pending, (fl.pending !! T).getD ⟨[], [], 0⟩ = P ∧
      pd = ⟨P.ids ++ runIds id n, P.alloctx ++ List.replicate n ((fl.allocs !! id).getD 0),
        P.lastReleaseBegin⟩) := by
  simp only [FLPg.freePages, GMap.lookup_insert_eq_iff] at h
  split at h
  · rename_i he; cases h; exact Or.inr ⟨he.symm, _, rfl, rfl⟩
  · rename_i he; exact Or.inl ⟨fun e => he e.symm, h⟩

private theorem freePages_pending_old (fl : FLPg) (T id : w64) (n : Nat) (t : w64) (pd : Pending)
    (h : fl.pending !! t = some pd) : ∃ pd', (fl.freePages T id n).pending !! t = some pd' ∧
      ∀ x, x ∈ pd.ids → x ∈ pd'.ids := by
  by_cases ht : t = T
  · subst ht
    refine ⟨⟨pd.ids ++ runIds id n, pd.alloctx ++ List.replicate n ((fl.allocs !! id).getD 0),
      pd.lastReleaseBegin⟩, by simp [FLPg.freePages, h], fun x hx => ?_⟩
    simp only [List.mem_append]; exact Or.inl hx
  · exact ⟨pd, by simp [FLPg.freePages, Ne.symm ht, h], fun x hx => hx⟩

private theorem pendSlots_free (fl : FLPg) (T id : w64) (n : Nat) (hn : id.toNat + n < 2 ^ 64) (s : Nat) :
    s ∈ pendSlots (fl.freePages T id n) ↔
      s ∈ pendSlots fl ∨ (id.toNat ≤ s ∧ s < id.toNat + n) := by
  rw [mem_pendSlots, mem_pendSlots]
  constructor
  · rintro ⟨t, pd, x, hp, hx, rfl⟩
    rcases freePages_lookup fl T id n t pd hp with ⟨-, hp⟩ | ⟨rfl, P, hP, rfl⟩
    · exact Or.inl ⟨t, pd, x, hp, hx, rfl⟩
    · simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · left
        rcases hq : fl.pending !! t with _ | q
        · rw [hq] at hP; simp only [Option.getD_none] at hP; subst hP; simp at hx
        · rw [hq] at hP; simp only [Option.getD_some] at hP; subst hP
          exact ⟨t, q, x, hq, hx, rfl⟩
      · exact Or.inr ((mem_runIds_toNat id n hn x).1 hx)
  · rintro (⟨t, pd, x, hp, hx, rfl⟩ | ⟨h1, h2⟩)
    · obtain ⟨pd', hp', hsub⟩ := freePages_pending_old fl T id n t pd hp
      exact ⟨t, pd', x, hp', hsub x hx, rfl⟩
    · refine ⟨T, _, W64 (s : Int), GMap.lookup_insert_eq _ _ _, ?_,
        W64_toNat_of_lt' s (by omega)⟩
      simp only [List.mem_append]
      right
      rw [mem_runIds_toNat id n hn, W64_toNat_of_lt' s (by omega)]; omega

private theorem freePages_self (fl : FLPg) (T id : w64) (n : Nat) :
    ∃ pd, (fl.freePages T id n).pending !! T = some pd ∧ ∀ x ∈ runIds id n, x ∈ pd.ids :=
  ⟨_, by simp only [FLPg.freePages]; exact GMap.lookup_insert _ _ _,
    fun _ hx => List.mem_append_right _ hx⟩

/-- `bytesWit` across a step that keeps the mapping, given the witness fact after and `fbInv`
after. -/
private theorem bytesWit_step (B : BNs) (σ σ' : StoreSt) (W : GMap Nat (List w8))
    (hms : σ'.ms = σ.ms)
    (hW : (∀ s ∈ storeSlots σ, W !! s = some (σ.bytes s)) →
      ∀ s ∈ storeSlots σ', W !! s = some (σ'.bytes s))
    (hfb : fbInv (GF := GF) B σ ⊢ fbInv B σ') :
    bytesWit (GF := GF) B σ W ⊢ bytesWit B σ' W := by
  unfold bytesWit
  rw [hms]
  iintro ⟨Hb1, Hb2, %hw, Hf⟩
  isplitl [Hb1]
  · iexact Hb1
  isplitl [Hb2]
  · iexact Hb2
  isplitr
  · ipureintro; exact hW hw
  iapply hfb; iexact Hf

/-! ### `fbInv` across the store's steps (batch 40B) -/

/-- `Free` of a run that does not hold the synced freelist page keeps `fbCond`. -/
private theorem fbCond_free_iff (C : CommitSt) (fl : FLPg) (wtx : Option Nat) (pb : Bool)
    (w : Nat) (id : w64) (n : Nat) (hwtx : wtx = some w)
    (hrun : ∀ x ∈ runIds id n, ∀ f, C.flpg = some f → ¬ coversSlot C.pages f → x.toNat ≠ f) :
    fbCond C (fl.freePages (W64 (w : Int)) id n) wtx pb ↔ fbCond C fl wtx pb := by
  subst hwtx
  constructor
  · rintro ⟨hpb, w', f, pd, hw', hf, hcov, hp, x, hx, hxf⟩
    cases hw'
    rcases freePages_lookup fl _ id n _ pd hp with ⟨hne, -⟩ | ⟨-, P, hP, rfl⟩
    · exact absurd rfl hne
    · simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · rcases hq : fl.pending !! W64 (w : Int) with _ | q
        · rw [hq] at hP; simp only [Option.getD_none] at hP; subst hP; simp at hx
        · rw [hq] at hP; simp only [Option.getD_some] at hP; subst hP
          exact ⟨hpb, w, f, q, rfl, hf, hcov, hq, x, hx, hxf⟩
      · exact absurd hxf (hrun x hx f hf hcov)
  · rintro ⟨hpb, w', f, pd, hw', hf, hcov, hp, x, hx, hxf⟩
    cases hw'
    obtain ⟨pd', hp', hsub⟩ := freePages_pending_old fl (W64 (w : Int)) id n _ pd hp
    exact ⟨hpb, w, f, pd', rfl, hf, hcov, hp', x, hsub x hx, hxf⟩

/-- The rolled-back writer has no pending entry: no `fbCond`. -/
private theorem fbCond_rollback (C : CommitSt) (fl : FLPg) (pb : Bool) (w : Nat) :
    ¬ fbCond C (fl.rollback (W64 (w : Int))) (some w) pb := by
  rintro ⟨-, w', f, pd, hw', -, -, hp, -⟩
  cases hw'
  unfold FLPg.rollback at hp
  split at hp
  · rename_i h; rw [h] at hp; cases hp
  · simp only [FLPg.rollbackEntry, GMap.lookup_delete] at hp; cases hp

omit go_gctx sem in
/-- `fbInv` across a step that keeps `fbCond` and, on its store slots, the bytes. -/
private theorem fbInv_mono (B : BNs) (σ σ' : StoreSt)
    (hc : fbCond σ.C σ.fl σ.wtx σ.pub → fbCond σ'.C σ'.fl σ'.wtx σ'.pub)
    (hc' : fbCond σ'.C σ'.fl σ'.wtx σ'.pub → fbCond σ.C σ.fl σ.wtx σ.pub)
    (hs : ∀ s ∈ storeSlots σ', s ∈ storeSlots σ ∧ σ'.bytes s = σ.bytes s) :
    fbInv (GF := GF) B σ ⊢ fbInv B σ' := by
  unfold fbInv
  iintro ⟨%F, H1, H2, %hok⟩
  iexists F
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · icases H2 with (H2 | %h)
    · ileft; iexact H2
    · iright; ipureintro; exact hc h
  ipureintro
  intro c s v hF hs'
  obtain ⟨hs1, hb⟩ := hs s hs'
  rw [hb]; exact hok (hc' c) s v hF hs1

/-- `fbInv` across a step without `fbCond` before and after (the token is home). -/
private theorem fbInv_nocond (B : BNs) (σ σ' : StoreSt) (h1 : ¬ fbCond σ.C σ.fl σ.wtx σ.pub)
    (h2 : ¬ fbCond σ'.C σ'.fl σ'.wtx σ'.pub) : fbInv (GF := GF) B σ ⊢ fbInv B σ' := by
  unfold fbInv
  iintro ⟨%F, H1, H2, -⟩
  iexists F
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · icases H2 with (H2 | %h)
    · ileft; iexact H2
    · exact absurd h h1
  ipureintro; intro c; exact absurd c h2

/-- `fbInv` with the token home before: the record set to `F'` (home after, or out with the
writer when `out`). -/
private theorem fbInv_set (B : BNs) (E : CoPset) (σ σ' : StoreSt) (F' : GMap Nat (List w8))
    (out : Bool)
    (hn : ¬ fbCond σ.C σ.fl σ.wtx σ.pub) (hout : out = true → fbCond σ'.C σ'.fl σ'.wtx σ'.pub)
    (hok : fbCond σ'.C σ'.fl σ'.wtx σ'.pub →
      ∀ s v, F' !! s = some v → s ∈ storeSlots σ' → σ'.bytes s = v) :
    fbInv (GF := GF) B σ ⊢ |={E}=> fbInv B σ' ∗
      (if out then ghostVar B.fpb (1 : Qp).half F' else iprop(emp)) := by
  unfold fbInv
  iintro ⟨%F, H1, H2, -⟩
  icases H2 with (H2 | %h)
  · imod ghostVar_update_halves F' B.fpb _ _ $$ H1 H2 with ⟨H1, H2⟩
    cases out
    · imodintro
      isplitl [H1 H2]
      · iexists F'
        isplitl [H1]
        · iexact H1
        isplitl [H2]
        · ileft; iexact H2
        ipureintro; exact hok
      · simp only [Bool.false_eq_true, ite_false]; iempintro
    · imodintro
      simp only [ite_true]
      isplitl [H1]
      · iexists F'
        isplitl [H1]
        · iexact H1
        isplitr
        · iright; ipureintro; exact hout rfl
        ipureintro; exact hok
      · iexact H2
  · exact absurd h hn

private theorem mem_storeSlots (σ : StoreSt) (s : Nat) :
    s ∈ storeSlots σ ↔ s ∈ treeSlots σ.C ∨ s ∈ pendSlots σ.fl := by
  simp only [storeSlots, mem_list_dedup, List.mem_append]

private theorem lent_none_of (σ : StoreSt) (s : Nat)
    (hR : ∀ k r, σ.R !! k = some r → ¬ coversSlot r.v.pages s)
    (hW : ∀ v, σ.wv = some v → σ.wlent = true → ¬ coversSlot v.pages s) : lent σ s = none := by
  classical
  have hfold : ∀ L : List (Nat × RdInfo), (∀ kv ∈ L, ¬ coversSlot kv.2.v.pages s) →
      L.foldr (fun kv acc => if coversSlot kv.2.v.pages s then optAdd rq acc else acc) none =
        none := by
    intro L hL
    induction L with
    | nil => rfl
    | cons kv L ih =>
      simp only [List.foldr_cons]
      rw [if_neg (hL kv (by simp)), ih fun kv' h => hL kv' (by simp [h])]
  unfold lent
  have hr : GMap.mapFold (fun _ (ri : RdInfo) acc =>
      if coversSlot ri.v.pages s then optAdd rq acc else acc) none σ.R = none :=
    hfold _ fun kv h => hR kv.1 kv.2 ((GMap.mem_toList _ _ _).1 h)
  rw [hr]
  split
  · rename_i v hv hl
    rw [if_neg (hW v hv hl)]
  · rfl

private theorem slots_leave_perm (σ σ' : StoreSt) (hsub : ∀ s ∈ storeSlots σ', s ∈ storeSlots σ) :
    (storeSlots σ).Perm (storeSlots σ' ++
      (storeSlots σ).filter (fun s => decide (s ∉ storeSlots σ'))) := by
  refine (List.perm_ext_iff_of_nodup (nodup_list_dedup _) ?_).2 fun s => ?_
  · refine List.nodup_append.2 ⟨nodup_list_dedup _, (nodup_list_dedup _).filter _,
      fun a ha b hb e => ?_⟩
    subst e; simp only [List.mem_filter, decide_eq_true_eq] at hb; exact hb.2 ha
  · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro hs; by_cases h : s ∈ storeSlots σ'
      · exact Or.inl h
      · exact Or.inr ⟨hs, h⟩
    · rintro (h | h)
      · exact hsub s h
      · exact h.1

private theorem slots_leave (p : BFile) (σ σ' : StoreSt) (hms : σ'.ms = σ.ms)
    (hb : σ'.bytes = σ.bytes) (hlent : lent σ' = lent σ)
    (hsub : ∀ s ∈ storeSlots σ', s ∈ storeSlots σ)
    (hnone : ∀ s ∈ storeSlots σ, s ∉ storeSlots σ' → lent σ s = none) :
    storeCells (GF := GF) σ ∗ ([∗list] s ∈ storeSlots σ, osSlot (GF := GF) p s (σ.bytes s)) ⊢
      storeCells σ' ∗ ([∗list] s ∈ storeSlots σ', osSlot p s (σ'.bytes s)) ∗
      slotsOwn σ.ms p ((storeSlots σ).filter (fun s => decide (s ∉ storeSlots σ'))) σ.bytes := by
  have hP := slots_leave_perm σ σ' hsub
  generalize hS : (storeSlots σ).filter (fun s => decide (s ∉ storeSlots σ')) = S at hP
  have hSm : ∀ s ∈ S, s ∈ storeSlots σ ∧ s ∉ storeSlots σ' := by
    intro s hs; rw [← hS] at hs; simp only [List.mem_filter, decide_eq_true_eq] at hs; exact hs
  rw [hb]
  unfold slotsOwn
  iintro ⟨Hc, Ho⟩
  ihave Ho := (BigSepL.bigSepL_perm hP).1 $$ Ho
  icases BigSepL.bigSepL_append.1 $$ Ho with ⟨Ho, HoS⟩
  rcases hm : σ.ms with _ | ⟨b, l⟩
  · have e1 : storeCells (GF := GF) σ = iprop(emp) := by unfold storeCells; rw [hm]
    have e2 : storeCells (GF := GF) σ' = iprop(emp) := by unfold storeCells; rw [hms, hm]
    rw [e1, e2]
    iframe
    iapply (BigSepL.bigSepL_sep_eqv).2
    isplitl []
    · iapply BigSepL.bigSepL_emp.2; iempintro
    · iexact HoS
  · rw [storeCells_some σ b l hm, storeCells_some σ' b l (hms.trans hm), hb, hlent]
    ihave Hc := (BigSepL.bigSepL_perm hP).1 $$ Hc
    icases BigSepL.bigSepL_append.1 $$ Hc with ⟨Hc, HcS⟩
    ihave HcS := (cells_unlent S (slotPt b σ.bytes) (lent σ)
      (fun s hs => hnone s (hSm s hs).1 (hSm s hs).2)).1 $$ HcS
    iframe
    iapply (BigSepL.bigSepL_sep_eqv).2
    iframe

private theorem fltx_all (B : BNs) (F : GMap Nat w64) (R : GMap Nat RdInfo) :
    ghostMapAuth B.fltx 1 F ∗
      ([∗map] k ↦ r ∈ R, k ↪[B.fltx] (W64 (r.v.txid : Int)) ∗ ghostVar B.mtok sync.rfrac ()) ⊢
    (ghostMapAuth (GF := GF) B.fltx 1 F ∗
      ([∗map] k ↦ r ∈ R, k ↪[B.fltx] (W64 (r.v.txid : Int)) ∗ ghostVar B.mtok sync.rfrac ())) ∗
    ⌜∀ k r, R !! k = some r → F !! k = some (W64 (r.v.txid : Int))⌝ := by
  refine sep_keep_pure ?_
  refine (forall_intro fun k => ?_).trans pure_forall.2
  refine (forall_intro fun r => ?_).trans pure_forall.2
  by_cases hk : R !! k = some r
  · refine (sep_mono .rfl (BigSepM.bigSepM_lookup (Φ := fun k' (r' : RdInfo) =>
      iprop(k' ↪[B.fltx] (W64 (r'.v.txid : Int)) ∗ ghostVar B.mtok sync.rfrac ())) hk)).trans ?_
    iintro ⟨Ha, Hf, -⟩
    ihave %h := ghost_map_lookup $$ Ha Hf
    ipureintro; exact fun _ => h
  · iintro -; ipureintro; exact fun h => absurd h hk

private theorem listDedup_sublist {α : Type} [DecidableEq α] (l : List α) : (listDedup l).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons a l ih =>
    unfold listDedup; split
    · exact ih.cons a
    · exact ih.cons₂ a

private def wUpd (W : GMap Nat (List w8)) (S : List Nat) (f : Nat → List w8) : GMap Nat (List w8) :=
  S.foldr (fun s m => m.insert s (f s)) W

private theorem wUpd_lookup (W : GMap Nat (List w8)) (S : List Nat) (f : Nat → List w8) (s : Nat) :
    wUpd W S f !! s = if s ∈ S then some (f s) else W !! s := by
  induction S with
  | nil => simp [wUpd]
  | cons a S ih =>
    simp only [wUpd, List.foldr_cons, GMap.lookup_insert_eq_iff] at ih ⊢
    by_cases h : a = s
    · subst h; simp
    · rw [if_neg h, ih]; simp [Ne.symm h]

private theorem slots_enter (p : BFile) (σ σ' : StoreSt) (S : List Nat) (bs : Nat → List w8)
    (hms : σ'.ms = σ.ms) (hlent : lent σ' = lent σ)
    (hperm : (storeSlots σ').Perm (storeSlots σ ++ S))
    (hold : ∀ s ∈ storeSlots σ, σ'.bytes s = σ.bytes s)
    (hnew : ∀ s ∈ S, σ'.bytes s = bs s ∧ lent σ s = none) :
    storeCells (GF := GF) σ ∗ ([∗list] s ∈ storeSlots σ, osSlot (GF := GF) p s (σ.bytes s)) ∗
      slotsOwn σ.ms p S bs ⊢
    storeCells σ' ∗ ([∗list] s ∈ storeSlots σ', osSlot p s (σ'.bytes s)) := by
  unfold slotsOwn
  iintro ⟨Hc, Ho, HS⟩
  icases (BigSepL.bigSepL_sep_eqv).1 $$ HS with ⟨HcS, HoS⟩
  isplitl [Hc HcS]
  · rcases hm : σ.ms with _ | ⟨b, l⟩
    · have e2 : storeCells (GF := GF) σ' = iprop(emp) := by unfold storeCells; rw [hms, hm]
      rw [e2]; iempintro
    · rw [storeCells_some σ b l hm, storeCells_some σ' b l (hms.trans hm), hlent]
      iapply (BigSepL.bigSepL_perm hperm).2
      iapply BigSepL.bigSepL_append.2
      isplitl [Hc]
      · iapply bigSepL_mono_mem (fun s hs => ?_) $$ Hc
        simp only [slotPt]; rw [hold s hs]
      · iapply (cells_unlent S (slotPt b σ'.bytes) (lent σ) (fun s hs => (hnew s hs).2)).2
        iapply bigSepL_mono_mem (fun s hs => ?_) $$ HcS
        simp only [slotPt]; rw [(hnew s hs).1]
  · iapply (BigSepL.bigSepL_perm hperm).2
    iapply BigSepL.bigSepL_append.2
    isplitl [Ho]
    · iapply bigSepL_mono_mem (fun s hs => ?_) $$ Ho
      rw [hold s hs]
    · iapply bigSepL_mono_mem (fun s hs => ?_) $$ HoS
      rw [(hnew s hs).1]

private theorem bigSepL_dedup {Φ : Nat → IProp GF} (S Sr : List Nat) (h : S.Perm (listDedup S ++ Sr)) :
    ([∗list] s ∈ S, Φ s) ⊢ [∗list] s ∈ listDedup S, Φ s :=
  BigSepL.bigSepL_submseteq h.symm

end helpers

/-! ## Mapped cells against the page cache (`store_cells_agree`'s steps, batch 30) -/

section agreeH
set_option linter.unusedSectionVars false

private theorem osBytes_cons' (p : BFile) (off : Nat) (dq : DFrac) (x : ByteG)
    (xs : List ByteG) :
    osBytes (GF := GF) p.ino off dq (x :: xs) ⊣⊢ osByte p.ino off dq x ∗ osBytes p.ino (off + 1) dq xs := by
  unfold osBytes osByte; exact bytesG_cons _ _ _ _ _ _

private theorem cellsR_cons' (base : Loc) (lo n : Nat) (vf : Nat → val) :
    cellsR (GF := GF) base lo (n + 1) vf ⊣⊢
      heapPointsto (base +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) (vf lo) ∗
        cellsR base (lo + 1) n vf := by
  unfold cellsR
  rw [List.range'_succ]
  exact BigSepL.bigSepL_cons

/-- The client halves of mapped cells `[lo, lo + xs.length)` hold the file's bytes `xs`, of which
a fraction is held, given the file's `OsMeta` (`osCell_agree` byte by byte); as `bytesPointsto`. -/
private theorem cellsR_agree_bytes (s : Stuckness) (E : CoPset) (e : Expr) (htv : toVal e = none)
    (p : BFile) (dqm : DFrac) (m : OsMeta)
    (base : Loc) (len : Nat) (hb : m.maps !! base = some len) (dqb : DFrac) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ∀ (xs : List ByteG) (lo : Nat) (vf : Nat → val), lo + xs.length ≤ len →
    ⊢ osInv -∗ osMeta p.ino dqm m -∗ osBytes p.ino lo dqb xs -∗
      cellsR base lo xs.length vf -∗
      (osMeta p.ino dqm m -∗ osBytes p.ino lo dqb xs -∗
        bytesPointsto (base +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) (xs.map Prod.fst) -∗
        WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }}
  | [], lo, vf, _ => by
    iintro #Hinv Hm Hb _ HΦ
    iapply HΦ $$ Hm Hb
    simp only [List.map_nil, bytesPointsto]
    itrivial
  | x :: xs, lo, vf, hl => by
    simp only [List.length_cons] at hl
    iintro #Hinv Hm Hb Hc HΦ
    icases (osBytes_cons' _ _ _ _ _).1 $$ Hb with ⟨Hx, Hb⟩
    simp only [List.length_cons]
    icases (cellsR_cons' _ _ _ _).1 $$ Hc with ⟨Hcx, Hc⟩
    iapply osCell_agree e htv p.ino dqm m base len lo hb (by omega) dqb x _ (vf lo) hE Φ
      $$ Hinv Hm Hx Hcx
    iintro %Hv Hm Hx Hcx
    iapply cellsR_agree_bytes s E e htv p dqm m base len hb dqb hE Φ xs (lo + 1) vf (by omega)
      $$ Hinv Hm Hb Hc
    iintro Hm Hb Hc
    iapply HΦ $$ Hm [Hx Hb] [Hcx Hc]
    · iapply (osBytes_cons' _ _ _ _ _).2; iframe
    · simp only [List.map_cons, bytesPointsto]
      rw [Hv]
      have e1 : base +ₗ ((lo : Nat) : Int) +ₗ 1 = base +ₗ (((lo + 1 : Nat) : Nat) : Int) := by
        rw [loc_add_assoc]; congr 1
      rw [e1]
      iframe

/-- `cellsR_agree_bytes` over whole store slots `S` (their page-cache bytes `osSlot`, of `4096`
bytes each, inside the mapping). -/
private theorem slots_agree_bytes (s : Stuckness) (E : CoPset) (e : Expr) (htv : toVal e = none)
    (p : BFile) (dqm : DFrac) (m : OsMeta)
    (base : Loc) (len : Nat) (hb : m.maps !! base = some len) (hE : ↑osN ⊆ E)
    (bs : Nat → List w8) (Φ : val → IProp GF) :
    ∀ (S : List Nat), (∀ t ∈ S, 4096 * (t + 1) ≤ len ∧ (bs t).length = 4096) →
    ⊢ osInv -∗ osMeta p.ino dqm m -∗ ([∗list] t ∈ S, osSlot p t (bs t)) -∗
      ([∗list] t ∈ S, ∃ vf, cellsR base (4096 * t) 4096 vf) -∗
      (osMeta p.ino dqm m -∗ ([∗list] t ∈ S, osSlot p t (bs t)) -∗
        ([∗list] t ∈ S,
          bytesPointsto (base +ₗ ((4096 * t : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs t)) -∗
        WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }}
  | [], _ => by
    iintro #Hinv Hm Ho _ HΦ
    iapply HΦ $$ Hm Ho
    iapply BigSepL.bigSepL_nil.2; iempintro
  | t :: S, hS => by
    iintro #Hinv Hm Ho Hc HΦ
    icases BigSepL.bigSepL_cons.1 $$ Ho with ⟨Hx, Ho⟩
    icases (show osSlot (GF := GF) p t (bs t) ⊢ ∃ xs : List ByteG,
        osBytes p.ino (4096 * t) (DFrac.own 1) xs ∗ ⌜xs.map Prod.fst = bs t⌝ by
        unfold osSlot; exact .rfl) $$ Hx with ⟨%xs, Hx, %Hxs⟩
    icases BigSepL.bigSepL_cons.1 $$ Hc with ⟨⟨%vf, Hcx⟩, Hc⟩
    obtain ⟨ht1, ht2⟩ := hS t (List.mem_cons_self ..)
    have hxl : xs.length = 4096 := by rw [← ht2, ← Hxs, List.length_map]
    have hc : cellsR (GF := GF) base (4096 * t) 4096 vf ⊢ cellsR base (4096 * t) xs.length vf := by
      rw [hxl]
    ihave Hcx := hc $$ Hcx
    iapply cellsR_agree_bytes s E e htv p dqm m base len hb (DFrac.own 1) hE Φ xs (4096 * t) vf
      (by omega) $$ Hinv Hm Hx Hcx
    iintro Hm Hx Hcx
    iapply slots_agree_bytes s E e htv p dqm m base len hb hE bs Φ S
      (fun u hu => hS u (List.mem_cons_of_mem _ hu)) $$ Hinv Hm Ho Hc
    iintro Hm Ho Hc
    iapply HΦ $$ Hm [Hx Ho] [Hcx Hc]
    · iapply BigSepL.bigSepL_cons.2
      iframe
      iapply (show (∃ xs : List ByteG, osBytes p.ino (4096 * t) (DFrac.own 1) xs ∗
          ⌜xs.map Prod.fst = bs t⌝) ⊢ osSlot (GF := GF) p t (bs t) by unfold osSlot; exact .rfl)
      iexists xs; iframe; ipureintro; exact Hxs
    · iapply BigSepL.bigSepL_cons.2
      iframe
      rw [Hxs]
      iexact Hcx


end agreeH

section lemmas
variable (B : BNs) (N : Namespace) (p : BFile) (E : CoPset) (hE : ↑(pagesN N) ⊆ E)
include hE

/-- `beginTx`, under `metalock` (`metaR`'s `cur`) and `Pm rfrac` (its `map` share and `mtok`):
register the reader `k` (its `fltx` fragment, inserted by the caller in `metaR`'s auth) with the
view of `C` at the mapping, borrowing `rq` of each of its slots and depositing `mtok rfrac`. -/
private theorem store_register_core (C : CommitSt) (b : Loc) (l k : Nat) (P Q : IProp GF)
    (hkeep : ∀ (R : GMap Nat RdInfo) (r : RdInfo) (o : Option Nat), R !! k = none →
      P ∗ ghostVar B.spr (1 : Qp).half.half o ∗ (opnShot B ∨ ⌜sprCl o R⌝) ⊢
      |={E \ ↑(pagesN N)}=> (∃ o' : Option Nat, ghostVar B.spr (1 : Qp).half.half o' ∗
        (opnShot B ∨ ⌜sprCl o' (<[k := r]> R)⌝)) ∗ Q) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗ ghostVar B.mtok sync.rfrac () ∗
      k ↪[B.fltx] (W64 (C.txid : Int)) ∗ P ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗
      k ↪[B.rds] (⟨View.ofC b C⟩ : RdInfo) ∗ viewCells rq (View.ofC b C) ∗ Q := by
  iintro ⟨#Hinv, Hcur, Hmap, Htok, Hfx, Hsp⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  subst hC
  have hms' : σ.ms = some (b, l) := hms.symm
  -- the key is fresh: a registered reader's deposit holds its `fltx` fragment
  rcases hk : σ.R !! k with _ | r0
  rotate_left
  · iexfalso
    icases (BigSepM.bigSepM_delete
      (Φ := fun k' (r' : RdInfo) => iprop(k' ↪[B.fltx] (W64 (r'.v.txid : Int)) ∗
        ghostVar B.mtok sync.rfrac ())) hk).1 $$ Hdep with ⟨⟨Hf, -⟩, -⟩
    ihave %h := ghostMapElem_valid_2 k B.fltx _ _ _ _ $$ Hfx Hf
    exfalso
    have := DFrac.valid_own_op h.1
    simp only [Qp.val_one] at this; exact absurd this (by decide)
  let r : RdInfo := ⟨View.ofC b σ.C⟩
  have hok' := storeOK_register σ k r b l Hok hms' hk rfl
  -- batch 41: the spare clause, kept (the opening is over, or the spare registers)
  unfold rdsAuth
  icases Hrds with ⟨Hrds, %o, Ho, Hcl⟩
  imod hkeep σ.R r o hk $$ [Hsp Ho Hcl] with ⟨Hspr, Hret⟩
  · iframe
  imod ghost_map_insert k r hk $$ Hrds with ⟨Hrds, Hk⟩
  ihave Hdep := (BigSepM.bigSepM_insert
    (Φ := fun k' (r' : RdInfo) => iprop(k' ↪[B.fltx] (W64 (r'.v.txid : Int)) ∗
      ghostVar B.mtok sync.rfrac ())) (m := σ.R) (i := k) (x := r) hk).2 $$ [Hfx Htok Hdep]
  · iframe
  icases sep_keep_pure (deposits_le (fun k' (r' : RdInfo) => iprop(k' ↪[B.fltx] (W64 (r'.v.txid : Int))))
    B.mtok sync.rfrac _) $$ Hdep with ⟨Hdep, %Hsz⟩
  have hrok := hok'.2.2.2.2.2.2.1 k r (by simp [StoreSt.register])
  obtain ⟨hTn, hTs, hTl⟩ := view_slots (σ.register k r) hok' r.v hrok.2.2.1 hrok.2.2.2.1
  rw [storeCells_some σ b l hms']
  icases cells_borrow (storeSlots σ) (pagesSlots r.v.pages) (nodup_list_dedup _) hTn hTs
    (slotPt b σ.bytes) (slotPt_add b σ.bytes) (lent σ) (lent (σ.register k r)) rq (1 : Qp).half
    (fun s _ => lent_register σ k r hk s)
    (fun s _ x hx => lent_lt_half2 (σ.register k r) Hsz s x hx)
    $$ Hcells with ⟨Hcells, Hv⟩
  have hvc := (viewCells_slots (GF := GF) rq r.v σ.bytes hrok.2.2.2.2.1 hTl).2
  rw [show r.v.base = b from rfl] at hvc
  ihave Hv := hvc $$ Hv
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hspr Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.register k r, W
    rw [storeCells_some (σ.register k r) b l hms']
    have e2 : metaLend (GF := GF) B (σ.register k r) = metaLend B σ := rfl
    have e3 : bytesWit (GF := GF) B (σ.register k r) W = bytesWit B σ W := rfl
    rw [e2, e3]
    have eR : (σ.register k r).R = <[k := r]> σ.R := rfl
    rw [eR]
    iframe
    try (isplitl [Hspr]; iexact Hspr)
    ipureintro
    exact hok'
  imodintro
  iframe

/-- A reader registers under the fresh key `k` (with its `fltx` fragment, deposited, and its
`mtok` share): the store's view of `C` at the mapping is lent to it. A pool reader: the opening is
over (`opnShot`, batch 41). -/
theorem store_register (C : CommitSt) (b : Loc) (l k : Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗ ghostVar B.mtok sync.rfrac () ∗
      k ↪[B.fltx] (W64 (C.txid : Int)) ∗ opnShot B ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗
      k ↪[B.rds] (⟨View.ofC b C⟩ : RdInfo) ∗ viewCells rq (View.ofC b C) := by
  iintro ⟨#Hinv, Hcur, Hmap, Htok, Hfx, #Hshot⟩
  imod store_register_core B N p E hE C b l k (opnShot B) emp (fun R r o _ => by
      iintro ⟨#Hs, Ho, -⟩
      imodintro
      isplitl
      · iexists o; iframe; ileft; iexact Hs
      · iempintro) $$ [Hinv Hcur Hmap Htok Hfx Hshot]
    with ⟨Hcur, Hmap, Hk, Hv, -⟩
  · iframe; iframe #
  imodintro; iframe

/-- **The spare reader registers** (batch 41, `beginTx_s` under `metalock`): as `store_register`,
and the spare state `B.spr` (the spare side's half `spareTok`, `metaR`'s quarter `o`, which was
`none`) set to its key. -/
theorem store_register_spare (C : CommitSt) (b : Loc) (l k : Nat) (o : Option Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗ ghostVar B.mtok sync.rfrac () ∗
      k ↪[B.fltx] (W64 (C.txid : Int)) ∗ spareTok B ∗ ghostVar B.spr (1 : Qp).half.half o ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗
      k ↪[B.rds] (⟨View.ofC b C⟩ : RdInfo) ∗ viewCells rq (View.ofC b C) ∗
      ghostVar B.spr (1 : Qp).half (some k) ∗ ghostVar B.spr (1 : Qp).half.half (some k) ∗
      ⌜o = none⌝ := by
  iintro ⟨#Hinv, Hcur, Hmap, Htok, Hfx, Hs2, Hs3⟩
  unfold spareTok
  icombine Hs2 Hs3 gives % ⟨_, ho⟩
  imod store_register_core B N p E hE C b l k
    (iprop(ghostVar B.spr (1 : Qp).half (none : Option Nat) ∗ ghostVar B.spr (1 : Qp).half.half o))
    (iprop(ghostVar B.spr (1 : Qp).half (some k) ∗ ghostVar B.spr (1 : Qp).half.half (some k)))
    (fun R r o0 _ => by
      iintro ⟨⟨H2, H3⟩, Ho, Hcl⟩
      imod spr_update B _ (some k) (o1 := none) (o2 := o0) (o3 := o) $$ [H2 Ho H3]
        with ⟨H2, Ho, H3, %ho0⟩
      · isplitl [H2]
        · iexact H2
        isplitl [Ho]
        · iexact Ho
        · iexact H3
      imodintro
      isplitr [H2 H3]
      · iexists (some k)
        isplitl [Ho]
        · iexact Ho
        icases Hcl with (Hs | %hcl)
        · ileft; iexact Hs
        · iright; ipureintro
          intro k' v hv
          rw [GMap.lookup_insert_eq_iff] at hv
          split at hv
          · rename_i he; rw [he]
          · have := hcl k' v hv; rw [ho0.1] at this; cases this
      · isplitl [H2]
        · iexact H2
        · iexact H3) $$ [Hinv Hcur Hmap Htok Hfx Hs2 Hs3]
    with ⟨Hcur, Hmap, Hk, Hv, Hs2, Hs3⟩
  · iframe Hcur Hmap Htok Hfx; iframe #
    isplitl [Hs2]
    · iexact Hs2
    · iexact Hs3
  imodintro
  iframe Hcur Hmap Hk Hv
  isplitl [Hs2]
  · iexact Hs2
  isplitl [Hs3]
  · iexact Hs3
  ipureintro; exact ho.symm

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
  unfold rdsAuth
  icases Hrds with ⟨Hrds, %o, Ho, Hcl⟩
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
  ihave Hspr : (∃ o' : Option Nat, ghostVar B.spr (1 : Qp).half.half o' ∗
      (opnShot B ∨ ⌜sprCl o' (σ.deregister k).R⌝)) $$ [Ho Hcl]
  · iexists o
    iframe Ho
    icases Hcl with (Hshot | %hcl)
    · ileft; iexact Hshot
    · iright; ipureintro
      intro k' v hv
      simp only [StoreSt.deregister] at hv
      rw [GMap.lookup_delete_iff] at hv
      split at hv
      · cases hv
      · exact hcl k' v hv
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hspr Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.deregister k, W
    rw [storeCells_some (σ.deregister k) b l hms]
    have e2 : metaLend (GF := GF) B (σ.deregister k) = metaLend B σ := rfl
    have e3 : bytesWit (GF := GF) B (σ.deregister k) W = bytesWit B σ W := rfl
    rw [e2, e3]
    iframe
    try (isplitl [Hspr]; iexact Hspr)
    ipureintro
    exact storeOK_deregister σ k Hok
  imodintro; iframe

/-- **The spare reader's state reset** (batch 41, `removeTx` of the spare reader under `metalock`,
after `store_deregister`): its `fltx` fragment shows it is no longer registered, so no reader is
(`sprCl`); the spare state back to `none` (the spare side's half `spareTok`, `metaR`'s quarter). -/
theorem store_spr_reset (k : Nat) (t : w64) (o : Option Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.spr (1 : Qp).half (some k) ∗
      ghostVar B.spr (1 : Qp).half.half o ∗ k ↪[B.fltx] t ⊢
    |={E}=> spareTok B ∗ ghostVar B.spr (1 : Qp).half.half (none : Option Nat) ∗ k ↪[B.fltx] t ∗
      ⌜o = some k⌝ := by
  iintro ⟨#Hinv, H2, H3, Hfx⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  unfold rdsAuth
  icases Hrds with ⟨Hrds, %o', Ho, Hcl⟩
  imod spr_update B _ none (o1 := some k) (o2 := o') (o3 := o) $$ [H2 Ho H3]
    with ⟨H2, Ho, H3, %ho⟩
  · isplitl [H2]
    · iexact H2
    isplitl [Ho]
    · iexact Ho
    · iexact H3
  -- the spare reader is not registered: its `fltx` fragment is not deposited
  ihave %hk : ⌜σ.R !! k = none⌝ $$ [Hdep Hfx]
  · rcases hk : σ.R !! k with _ | r0
    · ipureintro; rfl
    · iexfalso
      icases (BigSepM.bigSepM_delete
        (Φ := fun k' (r' : RdInfo) => iprop(k' ↪[B.fltx] (W64 (r'.v.txid : Int)) ∗
          ghostVar B.mtok sync.rfrac ())) hk).1 $$ Hdep with ⟨⟨Hf, -⟩, -⟩
      ihave %h := ghostMapElem_valid_2 k B.fltx _ _ _ _ $$ Hfx Hf
      exfalso
      have := DFrac.valid_own_op h.1
      simp only [Qp.val_one] at this; exact absurd this (by decide)
  ihave Hspr : (∃ o2 : Option Nat, ghostVar B.spr (1 : Qp).half.half o2 ∗
      (opnShot B ∨ ⌜sprCl o2 σ.R⌝)) $$ [Ho Hcl]
  · iexists none
    iframe Ho
    icases Hcl with (Hshot | %hcl)
    · ileft; iexact Hshot
    · iright; ipureintro
      intro k' v hv
      have h1 := hcl k' v hv
      rw [ho.1] at h1
      cases h1
      rw [hk] at hv; cases hv
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hspr Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ, W
    iframe
    try (isplitl [Hspr]; iexact Hspr)
    ipureintro; exact Hok
  imodintro
  unfold spareTok
  isplitl [H2]
  · iexact H2
  isplitl [H3]
  · iexact H3
  isplitl [Hfx]
  · iexact Hfx
  ipureintro; exact ho.2

/-- **`Open`'s loaded freelist into the store** (batch 41: was `DB__loadFreelist.open_setFl_gap`):
during the opening (`B.opn` at 1, `false`) with the spare pair idle (`spareTok`), no reader is
registered, so the store's empty freelist becomes the loaded one (`storeOK_setFl`). -/
theorem store_setFl (C : CommitSt) (fl : FLPg)
    (hfl : fl.WF ∧ fl.pending = ∅ ∧ flBelow fl C none ∧
      (∀ x ∈ fl.free, ¬ coversSlot C.pages x.toNat) ∧ fl.allocs = ∅) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half FLPg.empty ∗ ghostVar B.wv (1 : Qp).half wIdle ∗
      spareTok B ∗ dghostVar B.opn (DFrac.own 1) false ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.wv (1 : Qp).half wIdle ∗ spareTok B ∗ dghostVar B.opn (DFrac.own 1) false := by
  iintro ⟨#Hinv, Hcur, Hfl, Hwv, Hsp, Hopn⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl0⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  subst hC
  simp only [StoreSt.wst, wIdle, Prod.mk.injEq] at hws
  obtain ⟨hwv, hwtx, -, -⟩ := hws
  unfold rdsAuth spareTok
  icases Hrds with ⟨Hrds, %o, Ho, Hcl⟩
  icombine Hsp Ho gives % ⟨_, ho⟩
  icases Hcl with (#Hshot | %hcl)
  · iexfalso
    icases opnShot_pending B $$ [Hshot Hopn] with %hf
    · iframe; iframe #
    exact hf.elim
  have hR : σ.R = ∅ := by
    apply (GMap.lookup_empty_iff σ.R).1
    intro k
    rcases h : σ.R !! k with _ | v
    · rfl
    · have := hcl k v h; rw [← ho] at this; cases this
  ihave Hspr : (∃ o2 : Option Nat, ghostVar B.spr (1 : Qp).half.half o2 ∗
      (opnShot B ∨ ⌜sprCl o2 (σ.setFl fl).R⌝)) $$ [Ho]
  · iexists o; iframe Ho; iright; ipureintro; exact hcl
  have hok' := storeOK_setFl σ fl Hok hR hwtx.symm hwv.symm hfl
  imod ghostVar_update_halves fl B.fl _ _ $$ Hfl Hfl' with ⟨Hfl, Hfl'⟩
  have hps : pendSlots fl = pendSlots σ.fl := by
    rw [← hfl0]; unfold pendSlots FLPg.pendingIds; rw [hfl.2.1]; rfl
  have hss : storeSlots (σ.setFl fl) = storeSlots σ := by
    show listDedup (treeSlots σ.C ++ pendSlots fl) = listDedup (treeSlots σ.C ++ pendSlots σ.fl)
    rw [hps]
  have e1 : storeCells (GF := GF) (σ.setFl fl) = storeCells σ := by
    unfold storeCells; rw [hss]; rfl
  ihave Hbw := bytesWit_nocond B σ (σ.setFl fl) W rfl hss rfl
    (by rw [← hwtx]; exact fbCond_none _ _ _)
    (by show ¬ fbCond _ _ σ.wtx _; rw [← hwtx]; exact fbCond_none _ _ _) $$ Hbw
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hspr Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.setFl fl, W
    rw [e1, hss]
    have e2 : metaLend (GF := GF) B (σ.setFl fl) = metaLend B σ := rfl
    rw [e2]
    iframe
    try (isplitl [Hspr]; iexact Hspr)
    ipureintro; exact hok'
  imodintro
  iframe

/-- The writer's begin (after `store_release`): its txid the next, its base view (`C`'s at the
mapping) borrowed at `wq`. -/
theorem store_wbegin (C : CommitSt) (b : Loc) (l : Nat) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗ ghostVar B.wv (1 : Qp).half wIdle ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      ghostVar B.wv (1 : Qp).half ((some (View.ofC b C), some (C.txid + 1), false, true) : WSt) ∗
      viewCells wq (View.ofC b C) := by
  iintro ⟨#Hinv, Hcur, Hmap, Hwv⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  subst hC
  have hms' : σ.ms = some (b, l) := hms.symm
  simp only [StoreSt.wst, wIdle, Prod.mk.injEq] at hws
  obtain ⟨hwv, hwtx, -, -⟩ := hws
  let v := View.ofC b σ.C
  have hok' := storeOK_wbegin σ v b l Hok hms' hwtx.symm hwv.symm rfl
  icases sep_keep_pure (deposits_le (fun k' (r' : RdInfo) => iprop(k' ↪[B.fltx] (W64 (r'.v.txid : Int))))
    B.mtok sync.rfrac σ.R) $$ Hdep with ⟨Hdep, %Hsz⟩
  have hwok := hok'.2.2.2.2.2.2.2.1 v (by simp [StoreSt.wbegin, v])
  obtain ⟨hTn, hTs, hTl⟩ := view_slots (σ.wbegin v) hok' v hwok.2.2.1 hwok.2.2.2.1
  imod ghostVar_update_halves ((some v, some (σ.C.txid + 1), false, true) : WSt) B.wv _ _
    $$ Hwv Hwv' with ⟨Hwv, Hwv'⟩
  rw [storeCells_some σ b l hms']
  icases cells_borrow (storeSlots σ) (pagesSlots v.pages) (nodup_list_dedup _) hTn hTs
    (slotPt b σ.bytes) (slotPt_add b σ.bytes) (lent σ) (lent (σ.wbegin v)) wq (1 : Qp).half
    (fun s _ => lent_wbegin σ v hwv.symm s)
    (fun s _ x hx => lent_lt_half2 (σ.wbegin v) Hsz s x hx)
    $$ Hcells with ⟨Hcells, Hv⟩
  have hvc := (viewCells_slots (GF := GF) wq v σ.bytes hwok.2.2.2.2.1 hTl).2
  rw [show v.base = b from rfl] at hvc
  ihave Hv := hvc $$ Hv
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.wbegin v, W
    rw [storeCells_some (σ.wbegin v) b l hms']
    have e2 : metaLend (GF := GF) B (σ.wbegin v) = metaLend B σ := rfl
    rw [e2]
    ihave Hbw := bytesWit_nocond B σ (σ.wbegin v) W rfl rfl rfl
      (by rw [← hwtx]; exact fbCond_none _ _ _) (fbCond_wbegin σ Hok hwtx.symm) $$ Hbw
    iframe
    ipureintro
    exact hok'
  imodintro
  iframe

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
  iintro ⟨#Hinv, Hwv, Hv, Hfl⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  subst hfl
  simp only [StoreSt.wst, Prod.mk.injEq] at hws
  obtain ⟨hwv, hwtx, hpb, hwl⟩ := hws
  have hok' := storeOK_wclose σ Hok (by
    rcases hp with hp | hp
    · exact Or.inl (hpb ▸ hp)
    · exact Or.inr fun w' hw' => by rw [← hwtx] at hw'; cases hw'; exact hp)
  imod ghostVar_update_halves wIdle B.wv _ _ $$ Hwv Hwv' with ⟨Hwv, Hwv'⟩
  -- the cells: the view's returned when lent
  ihave Hcells : storeCells (GF := GF) σ.wclose $$ [Hcells Hv]
  · cases wl
    · simp only [Bool.false_eq_true, ite_false]
      have e : storeCells (GF := GF) σ.wclose = storeCells σ := by
        unfold storeCells; rw [lent_wclose (σ := σ) (hwl := hwl.symm)]; rfl
      rw [e]; iclear Hv; iexact Hcells
    · simp only [ite_true]
      obtain ⟨b, l, hms⟩ : ∃ b l, σ.ms = some (b, l) := by
        rcases hm : σ.ms with _ | ⟨b, l⟩
        · have := (Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hm).2; rw [← hwl] at this; cases this
        · exact ⟨b, l, rfl⟩
      have hwok := Hok.2.2.2.2.2.2.2.1 v hwv.symm
      have hbase : v.base = b := hwok.2.2.2.2.2.2 hwl.symm b l hms
      obtain ⟨hTn, hTs, hTl⟩ := view_slots σ Hok v hwok.2.2.1 hwok.2.2.2.1
      ihave Hv := (viewCells_slots wq v σ.bytes hwok.2.2.2.2.1 hTl).1 $$ Hv
      rw [hbase]
      rw [storeCells_some σ b l hms, storeCells_some σ.wclose b l hms]
      have e1 : storeSlots σ.wclose = storeSlots σ := rfl
      have e2 : σ.wclose.bytes = σ.bytes := rfl
      rw [e1, e2]
      iapply cells_return (storeSlots σ) (pagesSlots v.pages) (nodup_list_dedup _) hTn hTs
        (slotPt b σ.bytes) (slotPt_add b σ.bytes) (lent σ) (lent σ.wclose) wq (1 : Qp).half
        (fun s _ => by
          unfold lent; rw [← hwv, ← hwl]
          simp only [StoreSt.wclose]
          by_cases hc : coversSlot v.pages s
          · simp [hc, (mem_pagesSlots _ _).2 hc]
          · simp [hc, show s ∉ pagesSlots v.pages from fun h => hc ((mem_pagesSlots _ _).1 h)])
      iframe
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.wclose, W
    have e2 : metaLend (GF := GF) B σ.wclose = metaLend B σ := rfl
    rw [e2]
    ihave Hbw := bytesWit_nocond B σ σ.wclose W rfl rfl rfl
      (by
        rintro ⟨hpf, w', f, pd, hw', -, -, hpd, -⟩
        rw [← hwtx] at hw'; cases hw'
        rcases hp with hp | hp
        · rw [hpb] at hp; rw [hp] at hpf; cases hpf
        · rw [hp] at hpd; cases hpd)
      (fbCond_none _ _ _) $$ Hbw
    have ew : σ.wclose.wst = wIdle := rfl
    rw [ew]
    iframe
    ipureintro
    exact hok'
  imodintro; iframe

/-- `store_free`'s proof, with the `fpb` token taken out (`out`, the freelist page's case only)
or left home (batch 40B). -/
private theorem store_free_core (out : Bool) (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt)
    (w : Nat) (id : w64) (n : Nat) (pg : Nat → List w8) (hw : ws.2.1 = some w)
    (hpub : ws.2.2.1 = false) (hcan : fl.canFree (W64 (w : Int)) id n) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ws ∗
      ((⌜out = false ∧ ∃ q, C.pages !! id.toNat = some q ∧ 1 + pageOverflow q = n⌝) ∨
        (⌜0 < n ∧ C.flpg = some id.toNat ∧ ms ≠ none ∧ id.toNat + n ≤ C.hwm ∧
          ∀ j < n, ¬ coversSlot C.pages (id.toNat + j) ∧ (pg (id.toNat + j)).length = 4096 ∧
          ∀ b l, ms = some (b, l) → id.toNat + j < l / 4096⌝ ∗
          slotsOwn ms p (List.range' id.toNat n) pg)) ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half (fl.freePages (W64 (w : Int)) id n) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ∗
      (⌜out = false⌝ ∨ (ghostVar B.fpb (1 : Qp).half (fbRec id n pg) ∗
        ⌜fbCond C (fl.freePages (W64 (w : Int)) id n) ws.2.1 ws.2.2.1⌝)) := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hwv, Hcase⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  subst hC hfl hms hws
  have hwσ : σ.wtx = some w := hw
  have hpσ : σ.pub = false := hpub
  have hcn : id.toNat + n < 2 ^ 64 := hcan.2.1
  have hslt : ∀ s, s ∈ storeSlots σ → s < 2 ^ 64 := by
    intro s hs
    rw [mem_storeSlots] at hs
    rcases hs with hs | hs
    · exact treeSlot_lt64 σ Hok s ((mem_pagesSlots' _ _).1 hs)
    · obtain ⟨t, pd, x, -, -, rfl⟩ := (mem_pendSlots _ _).1 hs; exact x.isLt
  -- the run's store slots: the freed page's, or new
  have hstore : ∀ pg' s, s ∈ storeSlots (σ.free (W64 (w : Int)) id n pg') ↔
      s ∈ storeSlots σ ∨ (id.toNat ≤ s ∧ s < id.toNat + n) := by
    intro pg' s
    rw [mem_storeSlots, mem_storeSlots]
    simp only [StoreSt.free]
    rw [pendSlots_free σ.fl _ id n hcn s]
    exact or_assoc.symm
  imod ghostVar_update_halves (σ.fl.freePages (W64 (w : Int)) id n) B.fl _ _ $$ Hfl Hfl'
    with ⟨Hfl, Hfl'⟩
  icases Hcase with (%hA | ⟨%hB, HS⟩)
  · -- a page of the current tree: its slots are store slots already
    obtain ⟨hof, q, hq, hqn⟩ := hA
    subst hof
    let σ' := σ.free (W64 (w : Int)) id n σ.bytes
    have hok' := storeOK_free σ w id n σ.bytes Hok hwσ hpσ hcan (Or.inl ⟨⟨q, hq, hqn⟩,
      fun _ _ => rfl⟩)
    have hrun : ∀ s, id.toNat ≤ s → s < id.toNat + n → s ∈ storeSlots σ := fun s h1 h2 =>
      tree_in_store' σ s ⟨id.toNat, q, hq, h1, by omega⟩
    have hb : σ'.bytes = σ.bytes := by
      funext s; simp only [σ', StoreSt.free]; split <;> rfl
    have hperm : (storeSlots σ').Perm (storeSlots σ ++ []) := by
      rw [List.append_nil]
      refine (List.perm_ext_iff_of_nodup (nodup_list_dedup _) (nodup_list_dedup _)).2 fun s => ?_
      refine (hstore σ.bytes s).trans ⟨fun h => ?_, Or.inl⟩
      rcases h with h | h
      · exact h
      · exact hrun s h.1 h.2
    ihave Hcs := slots_enter p σ σ' [] σ.bytes rfl rfl hperm (fun s _ => by rw [hb])
      (fun s hs => by simp at hs) $$ [Hcells Hos]
    · iframe
      unfold slotsOwn
      iapply BigSepL.bigSepL_nil.2; iempintro
    icases Hcs with ⟨Hcells, Hos⟩
    imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with _
    · inext
      iexists σ', W
      have e2 : metaLend (GF := GF) B σ' = metaLend B σ := rfl
      rw [e2]
      have hrunNC : ∀ x ∈ runIds id n, ∀ f, σ.C.flpg = some f → ¬ coversSlot σ.C.pages f →
          x.toNat ≠ f := by
        intro x hx f _ hcov hxf
        obtain ⟨h1, h2⟩ := (mem_runIds_toNat id n hcn x).1 hx
        exact hcov ⟨id.toNat, q, hq, by omega, by omega⟩
      have hss : ∀ s ∈ storeSlots σ', s ∈ storeSlots σ ∧ σ'.bytes s = σ.bytes s := by
        intro s hs
        refine ⟨?_, by rw [hb]⟩
        rcases (hstore σ.bytes s).1 hs with h | h
        · exact h
        · exact hrun s h.1 h.2
      ihave Hbw := bytesWit_step B σ σ' W rfl
        (fun hW s hs => by rw [hb]; exact hW s (hss s hs).1)
        (fbInv_mono B σ σ' (fbCond_free_iff σ.C σ.fl σ.wtx σ.pub w id n hwσ hrunNC).2
          (fbCond_free_iff σ.C σ.fl σ.wtx σ.pub w id n hwσ hrunNC).1 hss) $$ Hbw
      iframe
      ipureintro; exact hok'
    imodintro; iframe
    try (ileft; ipureintro; rfl)
  · -- the old synced freelist page: its slots enter the store
    obtain ⟨hn, hflpg, hmsn, hhwm, hj⟩ := hB
    obtain ⟨b, l, hms'⟩ : ∃ b l, σ.ms = some (b, l) := by
      rcases hm : σ.ms with _ | ⟨b, l⟩
      · exact absurd hm hmsn
      · exact ⟨b, l, rfl⟩
    let σ' := σ.free (W64 (w : Int)) id n pg
    have hok' := storeOK_free σ w id n pg Hok hwσ hpσ hcan (Or.inr ⟨⟨hflpg, fun j hjn =>
      ⟨(hj j hjn).1, (hj j hjn).2.1, (hj j hjn).2.2⟩⟩, hhwm⟩)
    have hnew : ∀ s, id.toNat ≤ s → s < id.toNat + n → s ∉ storeSlots σ := by
      intro s h1 h2 hs
      rw [mem_storeSlots] at hs
      rcases hs with hs | hs
      · exact (hj (s - id.toNat) (by omega)).1 (by
          rw [show id.toNat + (s - id.toNat) = s by omega]; exact (mem_pagesSlots' _ _).1 hs)
      · obtain ⟨t, pd, x, hp, hx, hxs⟩ := (mem_pendSlots _ _).1 hs
        apply hcan.2.2.1 x ((mem_runIds_toNat id n hcn x).2 (by omega))
        simp only [FLPg.allIds, FLPg.pendingIds, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩
    have hbo : ∀ s, s ∈ storeSlots σ → σ'.bytes s = σ.bytes s := by
      intro s hs
      simp only [σ', StoreSt.free]
      rw [if_neg (fun h => hnew s ((inRun_W64 id n s (hslt s hs)).1 h).1
        ((inRun_W64 id n s (hslt s hs)).1 h).2 hs)]
    have hbn : ∀ s, id.toNat ≤ s → s < id.toNat + n → σ'.bytes s = pg s := by
      intro s h1 h2
      simp only [σ', StoreSt.free]
      rw [if_pos ((inRun_W64 id n s (by omega)).2 ⟨h1, h2⟩)]
    have hperm : (storeSlots σ').Perm (storeSlots σ ++ List.range' id.toNat n) := by
      refine (List.perm_ext_iff_of_nodup (nodup_list_dedup _) ?_).2 fun s => ?_
      · refine List.nodup_append.2 ⟨nodup_list_dedup _, List.nodup_range', fun a ha c hc e => ?_⟩
        subst e; simp only [List.mem_range'] at hc
        obtain ⟨j, hj', rfl⟩ := hc
        exact hnew (id.toNat + 1 * j) (by omega) (by omega) ha
      · refine (hstore pg s).trans ?_
        rw [List.mem_append, List.mem_range']
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨s - id.toNat, by omega, by omega⟩
        · rintro (h | ⟨j, hj', rfl⟩)
          · exact Or.inl h
          · exact Or.inr ⟨by omega, by omega⟩
    have hlent0 : ∀ s, id.toNat ≤ s → s < id.toNat + n → lent σ s = none := by
      intro s h1 h2
      refine lent_none_of σ s (fun k r hr hc => hnew s h1 h2 ((Hok.2.2.2.2.2.2.1 k r hr).2.2.1 s hc))
        (fun v hv _ hc => hnew s h1 h2 ((Hok.2.2.2.2.2.2.2.1 v hv).2.2.1 s hc))
    ihave Hcs := slots_enter p σ σ' (List.range' id.toNat n) pg rfl rfl hperm hbo
      (fun s hs => by
        simp only [List.mem_range'] at hs
        obtain ⟨j, hj', rfl⟩ := hs
        exact ⟨hbn _ (by omega) (by omega), hlent0 _ (by omega) (by omega)⟩) $$ [Hcells Hos HS]
    · iframe
    icases Hcs with ⟨Hcells, Hos⟩
    -- the bytes witness, updated with both halves
    -- batch 40B: the freed page's bytes recorded, the `fpb` token home or out
    have hcond0 : ¬ fbCond σ.C σ.fl σ.wtx σ.pub := by
      rintro ⟨-, w', f, pd, -, hf, -, hp, x, hx, hxf⟩
      rw [hflpg] at hf; cases hf
      have hxid : x = id := BitVec.eq_of_toNat_eq hxf
      rw [hxid] at hx
      apply hcan.2.2.1 id ((mem_runIds_toNat id n hcn id).2 ⟨Nat.le_refl _, by omega⟩)
      simp only [FLPg.allIds, FLPg.pendingIds, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(W64 (w' : Int), pd), (GMap.mem_toList _ _ _).2 hp, hx⟩
    have hcond1 : fbCond σ'.C σ'.fl σ'.wtx σ'.pub := by
      obtain ⟨pd, hpd, hmem⟩ := freePages_self σ.fl (W64 (w : Int)) id n
      exact ⟨hpσ, w, id.toNat, pd, hwσ, hflpg, (hj 0 hn).1, hpd, id,
        hmem id ((mem_runIds_toNat id n hcn id).2 ⟨Nat.le_refl _, by omega⟩), rfl⟩
    have hbook : fbCond σ'.C σ'.fl σ'.wtx σ'.pub →
        ∀ s v, fbRec id n pg !! s = some v → s ∈ storeSlots σ' → σ'.bytes s = v := by
      intro _ s v hv _
      rw [fbRec_lookup] at hv
      split at hv
      · rename_i hr
        cases hv
        simp only [List.mem_range'] at hr
        obtain ⟨j, hj', rfl⟩ := hr
        exact hbn _ (by omega) (by omega)
      · cases hv
    unfold bytesWit
    rw [hms']
    icases Hbw with ⟨Hb1, Hb2, %hW, Hfb⟩
    imod fbInv_set B _ σ σ' (fbRec id n pg) out hcond0 (fun _ => hcond1) hbook $$ Hfb
      with ⟨Hfb, Htok⟩
    imod ghostVar_update_halves (wUpd W (List.range' id.toNat n) pg) B.byt _ _ $$ Hb1 Hb2
      with ⟨Hb1, Hb2⟩
    imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hb1 Hb2 Hfb Hml] with _
    · inext
      iexists σ', wUpd W (List.range' id.toNat n) pg
      have e2 : metaLend (GF := GF) B σ' = metaLend B σ := rfl
      rw [e2, show σ'.ms = some (b, l) from hms']
      simp only
      iframe
      isplitr
      · ipureintro
        intro s hs
        rw [wUpd_lookup]
        have hs' := (hstore pg s).1 hs
        split
        · rename_i hr
          simp only [List.mem_range'] at hr
          obtain ⟨j, hj', rfl⟩ := hr
          rw [hbn (id.toNat + 1 * j) (by omega) (by omega)]
        · rename_i hr
          rcases hs' with hs' | hs'
          · rw [hbo s hs', hW s hs']
          · exact absurd (List.mem_range'.2 ⟨s - id.toNat, by omega, by omega⟩) hr
      · ipureintro; exact hok'
    imodintro
    iframe
    cases out
    · ileft; ipureintro; rfl
    · simp only [ite_true]
      iright
      isplitl [Htok]
      · iexact Htok
      · ipureintro; exact hcond1

/-- `Free(w, p)` of `n` slots from `id` by the live writer before its publish: a page of the
current tree, or the old synced freelist page (at least one slot), whose slots then move
`W → store` (F4.5); the freed page's bytes are recorded (`fbInv`), the `fpb` token stays home
(`Commit`'s free of the page is `store_free_fl`). -/
theorem store_free (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) (w : Nat) (id : w64)
    (n : Nat) (pg : Nat → List w8) (hw : ws.2.1 = some w) (hpub : ws.2.2.1 = false)
    (hcan : fl.canFree (W64 (w : Int)) id n) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ws ∗
      ((⌜∃ q, C.pages !! id.toNat = some q ∧ 1 + pageOverflow q = n⌝) ∨
        (⌜0 < n ∧ C.flpg = some id.toNat ∧ ms ≠ none ∧ id.toNat + n ≤ C.hwm ∧
          ∀ j < n, ¬ coversSlot C.pages (id.toNat + j) ∧ (pg (id.toNat + j)).length = 4096 ∧
          ∀ b l, ms = some (b, l) → id.toNat + j < l / 4096⌝ ∗
          slotsOwn ms p (List.range' id.toNat n) pg)) ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half (fl.freePages (W64 (w : Int)) id n) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hwv, Hcase⟩
  imod store_free_core B N p E hE false C fl ms ws w id n pg hw hpub hcan $$
    [Hinv Hcur Hfl Hmap Hwv Hcase] with ⟨Hcur, Hfl, Hmap, Hwv, -⟩
  · isplitr
    · iexact Hinv
    isplitl [Hcur]
    · iexact Hcur
    isplitl [Hfl]
    · iexact Hfl
    isplitl [Hmap]
    · iexact Hmap
    isplitl [Hwv]
    · iexact Hwv
    icases Hcase with (%hA | Hfp)
    · ileft; ipureintro; exact ⟨rfl, hA⟩
    · iright; iexact Hfp
  imodintro; iframe

/-- **`Commit`'s free of the old synced freelist page** (batch 40B, `commitFreelist`): as
`store_free`'s freelist-page case, and the writer takes the `fpb` token, which records the
page's bytes `pg` (`fbRec`): `store_rollback` returns them, `store_publish` takes it back. -/
theorem store_free_fl (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) (w : Nat) (id : w64)
    (n : Nat) (pg : Nat → List w8) (hw : ws.2.1 = some w) (hpub : ws.2.2.1 = false)
    (hcan : fl.canFree (W64 (w : Int)) id n) (hn : 0 < n) (hflpg : C.flpg = some id.toNat)
    (hmsn : ms ≠ none) (hhwm : id.toNat + n ≤ C.hwm)
    (hj : ∀ j < n, ¬ coversSlot C.pages (id.toNat + j) ∧ (pg (id.toNat + j)).length = 4096 ∧
      ∀ b l, ms = some (b, l) → id.toNat + j < l / 4096) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ws ∗ slotsOwn ms p (List.range' id.toNat n) pg ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half (fl.freePages (W64 (w : Int)) id n) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ∗
      fbTok B C (fl.freePages (W64 (w : Int)) id n) ws (fbRec id n pg) ∗
      ⌜fbCond C (fl.freePages (W64 (w : Int)) id n) ws.2.1 ws.2.2.1⌝ := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hwv, HS⟩
  imod store_free_core B N p E hE true C fl ms ws w id n pg hw hpub hcan $$
    [Hinv Hcur Hfl Hmap Hwv HS] with ⟨Hcur, Hfl, Hmap, Hwv, (%hf | ⟨Htok, %hc⟩)⟩
  · isplitr
    · iexact Hinv
    isplitl [Hcur]
    · iexact Hcur
    isplitl [Hfl]
    · iexact Hfl
    isplitl [Hmap]
    · iexact Hmap
    isplitl [Hwv]
    · iexact Hwv
    iright
    isplitr
    · ipureintro; exact ⟨hn, hflpg, hmsn, hhwm, hj⟩
    · iexact HS
  · cases hf
  imodintro
  iframe
  isplitl
  · unfold fbTok; ileft; iframe; ipureintro; exact hc
  · ipureintro; exact hc

/-- `Allocate` by the live writer: the ids leave the free list (their slots are `W` slots
already). -/
theorem store_alloc (fl : FLPg) (ws : WSt) (w : Nat) (r : w64) (n : Nat)
    (hw : ws.2.1 = some w) (ha : fl.canAlloc r n) (hn : 0 < n) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ghostVar B.fl (1 : Qp).half (fl.alloc (W64 (w : Int)) r n) ∗
      ghostVar B.wv (1 : Qp).half ws := by
  iintro ⟨#Hinv, Hfl, Hwv⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  subst hfl hws
  imod ghostVar_update_halves (σ.fl.alloc (W64 (w : Int)) r n) B.fl _ _ $$ Hfl Hfl' with ⟨Hfl, Hfl'⟩
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.alloc (W64 (w : Int)) r n, W
    have e1 : storeCells (GF := GF) (σ.alloc (W64 (w : Int)) r n) = storeCells σ := rfl
    have e2 : metaLend (GF := GF) B (σ.alloc (W64 (w : Int)) r n) = metaLend B σ := rfl
    have e3 : bytesWit (GF := GF) B (σ.alloc (W64 (w : Int)) r n) W = bytesWit B σ W := rfl
    rw [e1, e2, e3]
    iframe
    ipureintro
    exact storeOK_alloc σ w r n Hok hw ha hn
  imodintro; iframe

/-- `ReleasePendingPages` with no live writer, under `metalock` (`metaR`'s `F`, whose values are
`readonlyTXIDs` `ro`): the released slots move `store → W`, with their cells and bytes. -/
theorem store_release (C : CommitSt) (fl : FLPg) (ms : MapSt) (F : GMap Nat w64)
    (ro : List w64) (hro : ro.Perm (F.toList.map Prod.snd))
    (hro1 : ∀ k t, F !! k = some t → 1 ≤ t.toNat ∧ t.toNat ≤ C.txid) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half wIdle ∗ ghostMapAuth B.fltx 1 F ⊢
    |={E}=> ∃ (S : List Nat) (bs : Nat → List w8),
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half (fl.releasePending ro) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half wIdle ∗
      ghostMapAuth B.fltx 1 F ∗ slotsOwn ms p S bs ∗
      ⌜∀ s, s ∈ S ↔ s ∈ slotsOf C fl ∧ s ∉ slotsOf C (fl.releasePending ro)⌝ ∗
      ⌜∀ s ∈ S, (bs s).length = 4096⌝ := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hwv, Ha⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  subst hC hfl hms
  simp only [StoreSt.wst, wIdle, Prod.mk.injEq] at hws
  obtain ⟨hwv, hwtx, hpub, hwl⟩ := hws
  icases fltx_all B F σ.R $$ [Ha Hdep] with ⟨⟨Ha, Hdep⟩, %hF⟩
  · iframe
  have hroR : ∀ k r, σ.R !! k = some r → W64 (r.v.txid : Int) ∈ ro := by
    intro k r hr
    refine hro.symm.subset (List.mem_map.2 ⟨(k, _), (GMap.mem_toList _ _ _).2 (hF k r hr), rfl⟩)
  have hro' : ∀ t ∈ ro, t.toNat ≤ σ.C.txid ∧ 1 ≤ t.toNat := by
    intro t ht
    obtain ⟨⟨k, t'⟩, hkv, rfl⟩ := List.mem_map.1 (hro.subset ht)
    have := hro1 k _ ((GMap.mem_toList _ _ _).1 hkv)
    exact ⟨this.2, this.1⟩
  have hok' := storeOK_release σ ro Hok hwtx.symm hwl.symm hroR (fun t ht => (hro' t ht).1)
    (fun t ht => (hro' t ht).2)
  imod ghostVar_update_halves (σ.fl.releasePending ro) B.fl _ _ $$ Hfl Hfl' with ⟨Hfl, Hfl'⟩
  have hsub : ∀ s ∈ storeSlots (σ.release ro), s ∈ storeSlots σ := fun s hs =>
    storeSlots_release_sub σ ro (fun t ht => ⟨(hro' t ht).2, by
      have := (hro' t ht).1; have := Hok.2.1.2.2.2.2.2; omega⟩) Hok.2.2.2.1 s hs
  have hnone : ∀ s ∈ storeSlots σ, s ∉ storeSlots (σ.release ro) → lent σ s = none := by
    intro s _ hs'
    refine lent_none_of σ s (fun k r hr hc => hs' ?_) (fun v hv _ => by rw [← hwv] at hv; cases hv)
    exact (hok'.2.2.2.2.2.2.1 k r hr).2.2.1 s hc
  icases slots_leave p σ (σ.release ro) rfl rfl rfl hsub hnone $$ [Hcells Hos] with
    ⟨Hcells, Hos, HS⟩
  · iframe
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with _
  · inext
    iexists σ.release ro, W
    have e2 : metaLend (GF := GF) B (σ.release ro) = metaLend B σ := rfl
    rw [e2]
    ihave Hbw := bytesWit_step B σ (σ.release ro) W rfl (fun hW s hs => hW s (hsub s hs))
      (fbInv_nocond B σ (σ.release ro) (by rw [← hwtx]; exact fbCond_none _ _ _)
        (by show ¬ fbCond _ _ σ.wtx _; rw [← hwtx]; exact fbCond_none _ _ _)) $$ Hbw
    iframe
    ipureintro; exact hok'
  imodintro
  iexists _, σ.bytes
  iframe
  isplitr
  · ipureintro
    intro s
    simp only [List.mem_filter, decide_eq_true_eq, slotsOf]
    rfl
  -- batch 34: the released slots were store slots, whose bytes are whole pages (`storeOK`)
  ipureintro
  intro s hs
  simp only [List.mem_filter, decide_eq_true_eq] at hs
  exact (Hok.2.2.2.2.2.2.2.2.2.2.2.1 s hs.1).2

/-- **The commit point** (U10): the committed state moves `C → C'` (with `metaR`'s half and the
writer's quarter of `cur`), the new tree's slots `S` move `W → store` with their bytes; the
writer has published. The meta cells are out with the writer (`meta_take`, `out := true`: the
meta lend does not hold the old metas). The side conditions are spill's post (design §4.2). -/
theorem store_publish (C C' : CommitSt) (fl : FLPg) (ms : MapSt) (v : View) (w : Nat)
    (wl : Bool) (S : List Nat) (bs : Nat → List w8) (F : GMap Nat (List w8))
    (ht : C'.txid = w) (hmeta : C'.metaOk) (htree : treeOK C') (hhwm : C'.hwm ≤ 2 ^ 62)
    (hdrop : ∀ s ∈ treeSlots C, s ∉ treeSlots C' → s ∈ pendSlots fl)
    (hS : ∀ s, s ∈ S ↔ s ∈ treeSlots C' ∧ s ∉ slotsOf C fl)
    (hbytes : ∀ id pg, C'.pages !! id = some pg → C.pages !! id = some pg ∨
      ((∀ j < 1 + pageOverflow pg, id + j ∈ S) ∧
        pg = (List.range' id (1 + pageOverflow pg)).flatMap bs))
    (hfl : flBelow fl C' (some w)) (hnp : ∀ s ∈ treeSlots C', s ∉ pendSlots fl)
    (hSb : ∀ s ∈ S, (bs s).length = 4096 ∧ W64 (s : Int) ∉ fl.free ∧
      (∀ b l, ms = some (b, l) → s < l / 4096) ∧ 2 ≤ s) (hms : ms ≠ none) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ((some v, some w, false, wl) : WSt) ∗ slotsOwn ms p S bs ∗
      ghostVar B.out (1 : Qp).half true ∗ fbTok B C fl ((some v, some w, false, wl) : WSt) F ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half C' ∗ ghostVar B.cur (1 : Qp).half.half C' ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ((some v, some w, true, wl) : WSt) ∗
      ghostVar B.out (1 : Qp).half true := by
  iintro ⟨#Hinv, Hcur, Hcurq, Hfl, Hmap, Hwv, HS, Hout, Htok⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl'⟩
  icombine Hmap Hmap' gives % ⟨_, hms'⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  subst hC hfl' hms'
  simp only [StoreSt.wst, Prod.mk.injEq] at hws
  obtain ⟨hwv, hwtx, hpb, hwl⟩ := hws
  obtain ⟨b, l, hmsb⟩ : ∃ b l, σ.ms = some (b, l) := by
    rcases hm : σ.ms with _ | ⟨b, l⟩
    · exact absurd hm hms
    · exact ⟨b, l, rfl⟩
  -- the new slots: deduplicated
  have hSd := listDedup_sublist S
  obtain ⟨Sr, hSr⟩ := hSd.exists_perm_append
  have hS0 : ∀ s, s ∈ listDedup S ↔ s ∈ S := fun s => mem_list_dedup
  have hSnot : ∀ s ∈ S, s ∉ storeSlots σ := fun s hs => ((hS s).1 hs).2
  have hnew : ∀ s ∈ treeSlots C', s ∉ treeSlots σ.C → s ∉ pendSlots σ.fl ∧
      (∀ k r, σ.R !! k = some r → ¬ coversSlot r.v.pages s) ∧ (bs s).length = 4096 ∧
      W64 (s : Int) ∉ σ.fl.free ∧ (∀ b l, σ.ms = some (b, l) → s < l / 4096) ∧ 2 ≤ s := by
    intro s hs ht'
    have hsS : s ∈ S := (hS s).2 ⟨hs, fun h => by
      have h' : s ∈ storeSlots σ := h
      rw [mem_storeSlots] at h'
      rcases h' with h | h
      · exact ht' h
      · exact hnp s hs h⟩
    obtain ⟨h1, h2, h3, h4⟩ := hSb s hsS
    exact ⟨hnp s hs, fun k r hr hc => hSnot s hsS ((Hok.2.2.2.2.2.2.1 k r hr).2.2.1 s hc),
      h1, h2, h3, h4⟩
  have hok' := storeOK_publish σ w C' bs Hok hwtx.symm hpb.symm ht hmeta htree hhwm hdrop hnew
    hnp (fun id' pg hp => (hbytes id' pg hp).imp (fun h => h) fun ⟨h1, h2⟩ =>
      ⟨fun j hj => hSnot _ (h1 j hj), h2⟩) hfl
  let σ' := σ.publish C' bs
  have hbo : ∀ s ∈ storeSlots σ, σ'.bytes s = σ.bytes s := by
    intro s hs
    rw [mem_storeSlots] at hs
    simp only [σ', StoreSt.publish, if_pos hs]
  have hbn : ∀ s ∈ S, σ'.bytes s = bs s := by
    intro s hs
    have := hSnot s hs
    rw [mem_storeSlots] at this
    simp only [σ', StoreSt.publish, if_neg this]
  have hperm : (storeSlots σ').Perm (storeSlots σ ++ listDedup S) := by
    refine (List.perm_ext_iff_of_nodup (nodup_list_dedup _) ?_).2 fun s => ?_
    · refine List.nodup_append.2 ⟨nodup_list_dedup _, nodup_list_dedup _, fun a ha c hc e => ?_⟩
      subst e; exact hSnot a ((hS0 a).1 hc) ha
    · refine (mem_storeSlots σ' s).trans ?_
      rw [List.mem_append, hS0, mem_storeSlots]
      simp only [σ', StoreSt.publish]
      constructor
      · rintro (h | h)
        · by_cases ho : s ∈ treeSlots σ.C ∨ s ∈ pendSlots σ.fl
          · exact Or.inl ho
          · right; refine (hS s).2 ⟨h, fun h' => ho ?_⟩
            have h'' : s ∈ storeSlots σ := h'
            rwa [mem_storeSlots] at h''
        · exact Or.inl (Or.inr h)
      · rintro ((h | h) | h)
        · by_cases h' : s ∈ treeSlots C'
          · exact Or.inl h'
          · exact Or.inr (hdrop s h h')
        · exact Or.inr h
        · exact Or.inl ((hS s).1 h).1
  have hlent0 : ∀ s ∈ listDedup S, lent σ s = none := by
    intro s hs
    have hsS := (hS0 s).1 hs
    exact lent_none_of σ s (fun k r hr hc => hSnot s hsS ((Hok.2.2.2.2.2.2.1 k r hr).2.2.1 s hc))
      (fun v hv _ hc => hSnot s hsS ((Hok.2.2.2.2.2.2.2.1 v hv).2.2.1 s hc))
  -- the new slots, deduplicated (the rest dropped)
  unfold slotsOwn
  ihave HS := bigSepL_dedup S Sr hSr $$ HS
  ihave Hcs := slots_enter p σ σ' (listDedup S) bs rfl rfl hperm hbo
    (fun s hs => ⟨hbn s ((hS0 s).1 hs), hlent0 s hs⟩) $$ [Hcells Hos HS]
  · iframe; unfold slotsOwn; iexact HS
  icases Hcs with ⟨Hcells, Hos⟩
  -- the committed state, all three parts
  icases ((ghostVar_fractional (GF := GF) B.cur σ.C).fractional _ _).2 $$ [Hcur Hcurq] with Hc34
  · iframe
  imod ghostVar_update_2 C' B.cur _ _ _ _ (by
      rw [Qp.ext_iff]; simp only [Qp.val_add, Qp.val_half, Qp.val_one]; grind) $$ Hc34 Hcur'
    with ⟨Hc34, Hcur'⟩
  icases ((ghostVar_fractional (GF := GF) B.cur C').fractional _ _).1 $$ Hc34 with ⟨Hcur, Hcurq⟩
  imod ghostVar_update_halves ((some v, some w, true, wl) : WSt) B.wv _ _ $$ Hwv Hwv'
    with ⟨Hwv, Hwv'⟩
  -- the bytes witness
  unfold bytesWit
  rw [hmsb]
  icases Hbw with ⟨Hb1, Hb2, %hW, Hfb⟩
  icases fbInv_return B σ σ' ((some v, some w, false, wl) : WSt) F hwtx hpb (by
      rintro ⟨h, -⟩; simp [σ', StoreSt.publish] at h) $$ [Hfb Htok] with ⟨Hfb, -⟩
  · iframe
  imod ghostVar_update_halves (wUpd W (listDedup S) bs) B.byt _ _ $$ Hb1 Hb2 with ⟨Hb1, Hb2⟩
  -- the meta cells: out with the writer
  unfold metaLend
  icases Hml with (⟨-, Hout', -⟩ | Hml | ⟨Hout', -, -⟩)
  · icombine Hout Hout' gives % ⟨_, hb⟩; cases hb
  rotate_left
  · icombine Hout Hout' gives % ⟨_, hb⟩; cases hb
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hb1 Hb2 Hfb Hml] with _
  · inext
    iexists σ', wUpd W (listDedup S) bs
    rw [show σ'.ms = some (b, l) from hmsb]
    have ew : σ'.wst = ((some v, some w, true, wl) : WSt) := by
      simp only [σ', StoreSt.wst, StoreSt.publish, hwv, hwtx, hwl]
    rw [ew]
    simp only
    iframe
    isplitr
    · ipureintro
      intro s hs
      rw [wUpd_lookup]
      split
      · rename_i hr; rw [hbn s ((hS0 s).1 hr)]
      · rename_i hr
        rcases List.mem_append.1 (hperm.subset hs) with h | h
        · rw [hbo s h, hW s h]
        · exact absurd h hr
    · ipureintro; exact hok'
  imodintro; iframe

/-- `freelist.Rollback(w)` by the live writer before its publish: `w`'s pending pages are not
pending; slots leaving the store (B3: a freed old synced freelist page) move `store → W`. The
writer's `fbTok` goes back (batch 40B): when it had freed the synced freelist page
(`store_free_fl`), the bytes returned for the page's slots are the ones it recorded. -/
theorem store_rollback (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) (w : Nat)
    (F : GMap Nat (List w8)) (hw : ws.2.1 = some w) (hpub : ws.2.2.1 = false) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ws ∗ fbTok B C fl ws F ⊢
    |={E}=> ∃ (S : List Nat) (bs : Nat → List w8),
      ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half (fl.rollback (W64 (w : Int))) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ∗ slotsOwn ms p S bs ∗
      ⌜∀ s, s ∈ S ↔ s ∈ slotsOf C fl ∧ s ∉ slotsOf C (fl.rollback (W64 (w : Int)))⌝ ∗
      ⌜∀ s ∈ S, (bs s).length = 4096⌝ ∗
      ⌜fbCond C fl ws.2.1 ws.2.2.1 → ∀ s ∈ S, ∀ v, F !! s = some v → bs s = v⌝ := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hwv, Htok⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  subst hC hfl hms hws
  have hwσ : σ.wtx = some w := hw
  have hpσ : σ.pub = false := hpub
  have hok' := storeOK_rollback σ w Hok hwσ hpσ
  imod ghostVar_update_halves (σ.fl.rollback (W64 (w : Int))) B.fl _ _ $$ Hfl Hfl' with ⟨Hfl, Hfl'⟩
  have hsub : ∀ s ∈ storeSlots (σ.rollback (W64 (w : Int))), s ∈ storeSlots σ :=
    fun s hs => storeSlots_rollback_sub σ _ s hs
  have hnone : ∀ s ∈ storeSlots σ, s ∉ storeSlots (σ.rollback (W64 (w : Int))) →
      lent σ s = none := by
    intro s _ hs'
    exact lent_none_of σ s (fun k r hr hc => hs' ((hok'.2.2.2.2.2.2.1 k r hr).2.2.1 s hc))
      (fun v hv _ hc => hs' ((hok'.2.2.2.2.2.2.2.1 v hv).2.2.1 s hc))
  icases slots_leave p σ (σ.rollback (W64 (w : Int))) rfl rfl rfl hsub hnone $$ [Hcells Hos] with
    ⟨Hcells, Hos, HS⟩
  · iframe
  unfold bytesWit
  icases Hbw with ⟨Hb1, Hb2, %hW, Hfb⟩
  icases fbInv_return B σ (σ.rollback (W64 (w : Int))) σ.wst F rfl rfl
    (fun h => fbCond_rollback σ.C σ.fl σ.pub w (by rw [← hwσ]; exact h)) $$ [Hfb Htok]
    with ⟨Hfb, %hfb⟩
  · iframe
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hb1 Hb2 Hfb Hml] with _
  · inext
    iexists σ.rollback (W64 (w : Int)), W
    have e2 : metaLend (GF := GF) B (σ.rollback (W64 (w : Int))) = metaLend B σ := rfl
    rw [e2]
    simp only [StoreSt.rollback]
    iframe
    isplitr
    · ipureintro; intro s hs; exact hW s (hsub s hs)
    · ipureintro; exact hok'
  imodintro
  iexists _, σ.bytes
  iframe
  isplitr
  · ipureintro
    intro s
    simp only [List.mem_filter, decide_eq_true_eq, slotsOf]
    rfl
  isplitr
  · ipureintro
    intro s hs
    simp only [List.mem_filter, decide_eq_true_eq] at hs
    exact (Hok.2.2.2.2.2.2.2.2.2.2.2.1 s hs.1).2
  ipureintro
  intro hc s hs v hv
  simp only [List.mem_filter, decide_eq_true_eq] at hs
  exact hfb hc s v hv hs.1

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
      ⌜C.metaOk ∧ ∀ s ∈ slotsOf C fl, 2 ≤ s ∧ s < l / 4096 ∧ (bs s).length = 4096⌝ ∗
      ([∗list] s ∈ slotsOf C fl,
        bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s)) ∗
      metaCellsQ (1 : Qp).half.half (some (b, l)) C := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hmapq, Htok, Hwv, Hout⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  subst hC hfl hws
  have hms' : σ.ms = some (b, l) := hms.symm
  icases R_empty_of_tok B σ.R $$ [Hdep Htok] with ⟨⟨Hdep, Htok⟩, %hR⟩
  · iframe
  have hok' := storeOK_gather σ Hok hR hwl
  -- the cells: nothing lent
  rw [storeCells_some σ b l hms']
  ihave Hcells := (cells_unlent (storeSlots σ) (slotPt b σ.bytes) (lent σ)
    (fun s _ => lent_none σ hR hwl s)).1 $$ Hcells
  -- the meta cells: home
  unfold metaLend
  icases Hml with (⟨Hm, Hout', Hln⟩ | ⟨Hout', -, -⟩ | ⟨-, -, Htok'⟩)
  rotate_left
  · icombine Hout Hout' gives % ⟨_, hb⟩; cases hb
  · icombine Htok Htok' gives % ⟨hq, _⟩
    exfalso
    have := sync.rfrac.half.2
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    grind
  -- the bytes witness: the mapping's half out
  unfold bytesWit
  rw [hms']
  icases Hbw with ⟨Hb1, Hb2, %hW, Hfb⟩
  ihave Hfb := fbInv_mono B σ σ.gather id id (fun s hs => ⟨hs, rfl⟩) $$ Hfb
  -- the mapping's state: none
  icases ((ghostVar_fractional (GF := GF) B.map (some (b, l) : MapSt)).fractional _ _).2
    $$ [Hmap Hmapq] with Hm34
  · iframe
  imod ghostVar_update_2 (none : MapSt) B.map _ _ _ _ (by
      rw [Qp.ext_iff]; simp only [Qp.val_add, Qp.val_half, Qp.val_one]; grind) $$ Hm34 Hmap'
    with ⟨Hm34, Hmap'⟩
  icases ((ghostVar_fractional (GF := GF) B.map (none : MapSt)).fractional _ _).1 $$ Hm34
    with ⟨Hmap, Hmapq⟩
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hos Hb1 Hfb Hout' Hln] with _
  · inext
    iexists σ.gather, W
    have e1 : storeCells (GF := GF) σ.gather = iprop(emp) := by
      unfold storeCells; simp [StoreSt.gather]
    rw [e1]
    simp only [StoreSt.gather]
    iframe
    isplitr
    · ipureintro; exact hW
    isplitl [Hout' Hln]
    · ileft; iframe; unfold metaCellsQ; iempintro
    · ipureintro; exact hok'
  imodintro
  iexists σ.bytes, W
  iframe
  isplitr
  · ipureintro; exact hW
  ipureintro
  refine ⟨Hok.1, fun s hs => ?_⟩
  have h1 := Hok.2.2.2.2.2.2.2.2.2.2.2.1 s hs
  exact ⟨h1.1, Hok.2.2.2.2.2.2.2.2.2.2.2.2.1 b l hms' s hs, h1.2⟩

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
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hmapq, Htok, Hwv, Hbyt, Hcl, Hmc⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W', Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  subst hC hfl
  have hms' : σ.ms = none := hms.symm
  obtain ⟨hR, hwl⟩ := Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hms'
  have hok' := storeOK_carve σ b l Hok hms' hl
  unfold bytesWit
  rw [hms']
  icases Hbw with ⟨Hb1, -, %hW', Hfb⟩
  ihave Hfb := fbInv_mono B σ (σ.carve b l) id id (fun s hs => ⟨hs, rfl⟩) $$ Hfb
  icombine Hbyt Hb1 gives % ⟨_, hWW⟩
  subst hWW
  have hbs : ∀ s ∈ storeSlots σ, bs s = σ.bytes s := by
    intro s hs
    have h1 := hW s hs
    rw [hW' s hs] at h1
    exact (Option.some.inj h1).symm
  -- the mapping's state
  icases ((ghostVar_fractional (GF := GF) B.map (none : MapSt)).fractional _ _).2
    $$ [Hmap Hmapq] with Hm34
  · iframe
  imod ghostVar_update_2 (some (b, l) : MapSt) B.map _ _ _ _ (by
      rw [Qp.ext_iff]; simp only [Qp.val_add, Qp.val_half, Qp.val_one]; grind) $$ Hm34 Hmap'
    with ⟨Hm34, Hmap'⟩
  icases ((ghostVar_fractional (GF := GF) B.map (some (b, l) : MapSt)).fractional _ _).1 $$ Hm34
    with ⟨Hmap, Hmapq⟩
  -- the cells, unlent
  have hlent : ∀ s ∈ storeSlots (σ.carve b l), lent (σ.carve b l) s = none :=
    fun s _ => lent_none (σ.carve b l) hR hwl s
  ihave Hcells' : storeCells (GF := GF) (σ.carve b l) $$ [Hcl]
  · rw [storeCells_some (σ.carve b l) b l rfl]
    have e1 : storeSlots (σ.carve b l) = storeSlots σ := rfl
    have e2 : (σ.carve b l).bytes = σ.bytes := rfl
    rw [e1, e2]
    iapply (cells_unlent (storeSlots σ) (slotPt b σ.bytes) (lent (σ.carve b l))
      (fun s hs => hlent s hs)).2
    have hconv : ([∗list] s ∈ storeSlots σ,
        bytesPointsto (GF := GF) (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s)) ⊢
        [∗list] s ∈ storeSlots σ, slotPt b σ.bytes s (1 : Qp).half :=
      bigSepL_mono_mem fun s hs => by simp only [slotPt]; rw [hbs s hs]
    iapply hconv
    rw [show slotsOf σ.C σ.fl = storeSlots σ from rfl]
    iexact Hcl
  -- the meta cells: back home
  unfold metaLend
  icases Hml with (⟨-, Hout', Hln⟩ | Hml2 | ⟨-, -, Htok'⟩)
  · imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells' Hos Hb1 Hbyt Hfb Hout' Hln Hmc] with _
    · inext
      iexists σ.carve b l, W
      simp only [StoreSt.carve]
      iframe
      isplitr
      · ipureintro; exact hW'
      isplitl [Hout' Hln Hmc]
      · ileft; iframe
      · ipureintro; exact hok'
    imodintro; iframe
  · iclear Hmc
    imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells' Hos Hb1 Hbyt Hfb Hml2] with _
    · inext
      iexists σ.carve b l, W
      simp only [StoreSt.carve]
      iframe
      isplitr
      · ipureintro; exact hW'
      ipureintro; exact hok'
    imodintro; iframe
  · icombine Htok Htok' gives % ⟨hq, _⟩
    exfalso
    have := sync.rfrac.half.2
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    grind

/-- `beginTx`'s `t.init` under `metalock` and `Pm rfrac`: the reader deposits `mlk` and
`mtok (rfrac/2)` and borrows the meta cells' quarter. -/
theorem meta_borrow (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.mlk 1 () ∗
      ghostVar B.mtok sync.rfrac.half () ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half ms ⊢
    |={E}=> metaCellsQ (1 : Qp).half.half ms C ∗ ghostVar B.mln 1 () ∗
      ghostVar B.cur (1 : Qp).half C ∗ ghostVar B.map sync.rfrac.half.half ms := by
  iintro ⟨#Hinv, Hmlk, Htok, Hcur, Hmap⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl, Hmap', Hwv, Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  subst hC hms
  unfold metaLend
  icases Hml with (⟨Hm, Hout', Hln⟩ | ⟨-, Hmlk', -⟩ | ⟨-, Hmlk', -⟩)
  · imod Hclose $$ [Hcur' Hfl Hmap' Hwv Hrds Hdep Hcells Hos Hbw Hout' Hmlk Htok] with _
    · inext; iexists σ, W; iframe
      isplitl [Hout' Hmlk Htok]
      · iright; iright; iframe
      ipureintro; exact Hok
    imodintro; iframe
  all_goals
    icombine Hmlk Hmlk' gives % ⟨hq, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    grind

/-- The reader gives the meta cells' quarter back and gets its deposits. -/
theorem meta_return (C : CommitSt) (ms : MapSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ metaCellsQ (1 : Qp).half.half ms C ∗
      ghostVar B.mln 1 () ∗ ghostVar B.cur (1 : Qp).half C ∗
      ghostVar B.map sync.rfrac.half.half ms ⊢
    |={E}=> ghostVar B.mlk 1 () ∗ ghostVar B.mtok sync.rfrac.half () ∗
      ghostVar B.cur (1 : Qp).half C ∗ ghostVar B.map sync.rfrac.half.half ms := by
  iintro ⟨#Hinv, Hm, Hln, Hcur, Hmap⟩
  have := pagesInv_timeless (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl, Hmap', Hwv, Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  subst hC hms
  unfold metaLend
  icases Hml with (⟨-, -, Hln'⟩ | ⟨-, -, Hln'⟩ | ⟨Hout', Hmlk, Htok⟩)
  rotate_left 2
  · imod Hclose $$ [Hcur' Hfl Hmap' Hwv Hrds Hdep Hcells Hos Hbw Hout' Hm Hln] with _
    · inext; iexists σ, W; iframe
      isplitl [Hout' Hm Hln]
      · ileft; iframe
      ipureintro; exact Hok
    imodintro; iframe
  all_goals
    icombine Hln Hln' gives % ⟨hq, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    grind

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

/-- **The new mapping's store cells hold the store's bytes** (batch 15, U4's remap, before
`store_carve`): in one atomic step `e` (e.g. the store of `db.dataref` after `mmap`), with the
mapping `(b, l)` in the file's `OsMeta` and the client halves of the store slots' cells (any
values: `mmap`'s cells), the cells hold the bytes the store's witness `W` records (the half
`store_gather` handed out): `pagesInv`'s page-cache bytes of each store slot, read with OsFs's
`osCell_agree` byte by byte (as the bboltfs example's `cellsR_agree`), while it is open around
`e` (so the continuation runs without `pagesN N`). The result is `store_carve`'s premises `hW` and the cells. Owner: the maintainer (U3's
successor). -/
theorem store_cells_agree (s : Stuckness) (e : Expr) (htv : toVal e = none)
    (ι : Iris.ProgramLogic.Language.Atomic ↑s e) (hE' : ↑osN ⊆ E \ ↑(pagesN N)) (C : CommitSt) (fl : FLPg)
    (ws : WSt) (b : Loc) (l : Nat) (m : OsMeta) (dqm : DFrac) (W : GMap Nat (List w8))
    (hb : m.maps !! b = some l) (hl : ∀ s ∈ slotsOf C fl, s < l / 4096) (Φ : val → IProp GF) :
    ⊢ inv (pagesN N) (pagesInv (GF := GF) B p) -∗ osInv -∗
      ghostVar B.cur (1 : Qp).half.half C -∗ ghostVar B.fl (1 : Qp).half fl -∗
      ghostVar B.map (1 : Qp).half (none : MapSt) -∗ ghostVar B.wv (1 : Qp).half ws -∗
      ghostVar B.byt (1 : Qp).half W -∗ osMeta p.ino dqm m -∗
      ([∗list] s ∈ slotsOf C fl, ∃ vf, cellsR b (4096 * s) 4096 vf) -∗
      (∀ bs : Nat → List w8, ⌜∀ s ∈ slotsOf C fl, W !! s = some (bs s)⌝ -∗
        ghostVar B.cur (1 : Qp).half.half C -∗ ghostVar B.fl (1 : Qp).half fl -∗
        ghostVar B.map (1 : Qp).half (none : MapSt) -∗ ghostVar B.wv (1 : Qp).half ws -∗
        ghostVar B.byt (1 : Qp).half W -∗ osMeta p.ino dqm m -∗
        ([∗list] s ∈ slotsOf C fl,
          bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s)) -∗
        WP e @ s; (E \ ↑(pagesN N)) {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  iintro #Hinv #Hos Hcur Hfl Hmap Hwv Hbyt Hm Hcells Hk
  have := pagesInv_timeless (GF := GF) B p
  iapply wp_atomic (E2 := E \ ↑(pagesN N))
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W', Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells', Hos', Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hF⟩
  unfold bytesWit
  icases Hbw with ⟨Hbyt', Hbm, %Hwit, Hfb⟩
  icombine Hbyt Hbyt' gives % ⟨_, hW⟩
  subst hC hF hW
  have hS : storeSlots σ = slotsOf σ.C σ.fl := rfl
  have hlen := Hok.2.2.2.2.2.2.2.2.2.2.2.1
  imodintro
  iapply slots_agree_bytes s (E \ ↑(pagesN N)) e htv p dqm m b l hb hE' σ.bytes _ (slotsOf σ.C σ.fl)
    (fun t ht => ⟨by have := hl t ht; omega, (hlen t (hS ▸ ht)).2⟩) $$ Hos Hm [Hos'] Hcells
  · rw [hS]; iexact Hos'
  iintro Hm Hos' Hcells
  ihave Hwp := Hk $$ %σ.bytes %(fun t ht => Hwit t (hS ▸ ht)) Hcur Hfl Hmap Hwv Hbyt Hm Hcells
  iapply wp_wand $$ Hwp
  iintro %v HΦ
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells' Hos' Hbyt' Hbm Hfb Hml] with _
  · inext; iexists σ, W; iframe
    rw [hS]; iframe
    ipureintro; exact ⟨Hwit, Hok⟩
  imodintro; iexact HΦ


end lemmas

end store

end bbolt
end EtcdGrove
end Perennial
