/-
The Iris side of a new writer's state (U5 of `notes/bbolt-proof-plan.md`; design §3.11 "Writer
begin"): the store's state read under the writer side's ghost halves (`store_ok_read`), the
freelist object is not nil (`flPgOwn_ok`), the initial heap `wtxHeap` of `wx0` from `Tx.init`'s
fields (`wtxHeap_wx0`), its page tokens (`txShape_wx0`) and the writer's names
(`wr_names_alloc`).
-/
module

public import Proof.go_etcd_io.bbolt.Txn.WInit
public import Proof.go_etcd_io.bbolt.Txn.RdReg
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section winit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit go_gctx sem in
private theorem pagesInv_timeless_w (B : BNs) (p : GoString) : Timeless (pagesInv (GF := GF) B p) := by
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

section store
variable (B : BNs) (N : Namespace) (p : GoString) (E : CoPset) (hE : ↑(pagesN N) ⊆ E)
include hE

omit sem in
/-- **The store's state, read** by the writer side's ghost halves (`rwlock`'s): its committed
state, freelist, mapping and writer state are theirs, and it is `storeOK`. -/
theorem store_ok_read (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ∗
      ⌜∃ σ : StoreSt, σ.C = C ∧ σ.fl = fl ∧ σ.ms = ms ∧ σ.wst = ws ∧ storeOK σ⌝ := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hwv⟩
  have := pagesInv_timeless_w (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with -
  · inext; iexists σ, W; iframe; ipureintro; exact Hok
  imodintro
  iframe
  ipureintro
  exact ⟨σ, hC.symm, hfl.symm, hms.symm, hws.symm, Hok⟩

end store

omit hos in
/-- The freelist object is not nil (its implementation's interface value). -/
theorem flPgOwn_ok (fli : GoInterface) (fl : FLPg) :
    flPgOwn (GF := GF) fli fl ⊢ ⌜fli ≠ interface.nil⌝ := by
  unfold flPgOwn flImplAt
  iintro ⟨%a, %s, %al, %ca, %pe, %c, %pp, Hi, -⟩
  icases Hi with (⟨%h, -⟩ | ⟨%h, -⟩) <;> ipureintro <;> subst h <;> simp [interface.mkOk]

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
theorem objs_wx0 (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket)
    (v : View) : (wx0 rl t mv bv ib v).t.objs = ∅ := by
  have key : ∀ (l : List (Loc × BRec)) (m : GMap Loc WObj), (∀ x ∈ l, x.2.ns = ∅) →
      l.foldl (fun m bB => bB.2.ns.toList.foldl
        (fun m' lr => m'.insert lr.1 (.node bB.1 lr.2)) m) m = m := by
    intro l; induction l with
    | nil => intro m _; rfl
    | cons a l ih =>
      intro m h
      simp only [List.foldl_cons]
      rw [h a List.mem_cons_self, GMap.toList_empty, List.foldl_nil]
      exact ih m (fun x hx => h x (List.mem_cons_of_mem _ hx))
  unfold WTx.objs
  rw [key]
  · apply GMap.ext; intro k; simp [wx0]
  · intro x hx
    have := (GMap.mem_toList _ _ _).1 hx
    simp only [wx0] at this
    obtain ⟨-, h⟩ := wx0_bs_some rl t mv bv ib v x.1 x.2 (by simpa [wx0] using this)
    rw [h]; rfl

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
theorem bobjs_wx0 (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket)
    (v : View) : (wx0 rl t mv bv ib v).t.bobjs = GMap.singleton rl (brec0 bv ib) := by
  apply GMap.ext; intro k
  simp [WTx.bobjs, wx0]

/-- The `Tx` record a writer's `Tx.init` leaves (its `db`, `root` and `stats` fields are not
`txFields`'). -/
def tx0 (tx bm nm ibp m pm : Loc) (ch : GoSlice) (wf : w64) : Tx :=
  ⟨true, false, null, m, initRoot tx bm nm ibp, pm, zeroValDef, ch, wf⟩

omit hos in
/-- **The initial writer heap** (`wx0`), from `Tx.init`'s writer fields: the transaction's fields,
the meta copy, the empty page cache, the root bucket's fields, header and empty caches. -/
theorem wtxHeap_wx0 (tx bm nm ibp m pm : Loc) (ch : GoSlice) (wf : w64) (mv : go_etcd_io.bbolt.internal.common.Meta)
    (ib : InBucket) (v : View) :
    tx.[Tx, go!"writable"] ↦ true ∗ tx.[Tx, go!"managed"] ↦ false ∗ tx.[Tx, go!"meta"] ↦ m ∗
      tx.[Tx, go!"pages"] ↦ pm ∗ tx.[Tx, go!"commitHandlers"] ↦ ch ∗
      tx.[Tx, go!"WriteFlag"] ↦ wf ∗ (m ↦ mv : IProp GF) ∗ pm ↦$ (∅ : GMap w64 Loc) ∗
      (txRoot (GF := GF) tx).[Bucket, go!"InBucket"] ↦ ibp ∗ (txRoot (GF := GF) tx).[Bucket, go!"tx"] ↦ tx ∗
      (txRoot (GF := GF) tx).[Bucket, go!"buckets"] ↦ bm ∗ (txRoot (GF := GF) tx).[Bucket, go!"page"] ↦ null ∗
      (txRoot (GF := GF) tx).[Bucket, go!"rootNode"] ↦ null ∗
      (txRoot (GF := GF) tx).[Bucket, go!"nodes"] ↦ nm ∗
      (txRoot (GF := GF) tx).[Bucket, go!"FillPercent"] ↦ W64 4602678819172646912 ∗
      ibp ↦ ib ∗ nm ↦$ (∅ : GMap w64 Loc) ∗ bm ↦$ (∅ : GMap GoString Loc) ⊢
    wtxHeap tx (DFrac.own 1)
      (wx0 (txRoot (GF := GF) tx) (tx0 tx bm nm ibp m pm ch wf) mv (initRoot tx bm nm ibp) ib v) := by
  iintro ⟨Hw, Hmg, Hme, Hpg, Hch, Hwf, Hmv, Hpm, Hib, Htx, Hbk, Hpp, Hrn, Hnd, Hfp, Hibv, Hnm, Hbm⟩
  ihave %Hnmn := ownMap_not_nil _ _ _ $$ Hnm
  have Hnmn' : nm ≠ null := Hnmn
  unfold wtxHeap
  rw [objs_wx0, bobjs_wx0]
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro bl B hb n hn
      obtain ⟨-, rfl⟩ := wx0_bs_some _ _ _ _ _ _ bl B hb
      simp [brec0] at hn
    · intro bl B hb
      obtain ⟨-, rfl⟩ := wx0_bs_some _ _ _ _ _ _ bl B hb
      exact ⟨rfl, Hnmn'⟩
    · intro bl B n r hb hn
      obtain ⟨-, rfl⟩ := wx0_bs_some _ _ _ _ _ _ bl B hb
      simp [brec0] at hn
    · intro n y h; simp [wx0] at h
    · intro bl B hb
      left; exact (wx0_bs_some _ _ _ _ _ _ bl B hb).1
  isplitl [Hw Hmg Hme Hpg Hch Hwf Hmv Hpm]
  · unfold txFields
    simp only [wx0, tx0]
    iframe
    simp; iempintro
  isplitl [Hfp]
  · unfold rootFill txRoot; iexists W64 4602678819172646912; iframe Hfp; ipureintro; exact fill_default_not_nan
  isplitl []
  · simp; iempintro
  rw [show GMap.singleton (txRoot (GF := GF) tx) (brec0 (initRoot tx bm nm ibp) ib) =
    Std.insert (∅ : GMap Loc BRec) (txRoot (GF := GF) tx) (brec0 (initRoot tx bm nm ibp) ib) from rfl]
  iapply (BigSepM.bigSepM_insert (M := GMap Loc) (m := (∅ : GMap Loc BRec)) (i := txRoot (GF := GF) tx)
    (x := brec0 (initRoot tx bm nm ibp) ib) (by rfl)).2
  isplitl
  rotate_left
  · iapply BigSepM.bigSepM_empty.2; iempintro
  unfold objOwn pageOwn
  have hrl : txRoot (GF := GF) tx = tx.[Tx, go!"root"] := rfl
  simp only [brec0, initRoot, newBucketV, wx0]
  simp only [← hrl, ↓reduceIte, Hnmn', if_false]
  iframe
  split <;> iempintro

omit hos sem in
/-- A big separating conjunction over a map's keys, through `fmap` to `Unit`. -/
theorem bigSepM_fmap_unit (Φ : Nat → Unit → IProp GF) :
    ∀ P : Pages, ([∗map] k ↦ v ∈ P.fmap (fun _ => ()), Φ k v) ⊣⊢ [∗map] k ↦ _x ∈ P, Φ k () := by
  apply GMap.map_ind
  · rw [GMap.fmap_empty]
    exact (BigSepM.bigSepM_empty (M := GMap Nat)).trans (BigSepM.bigSepM_empty (M := GMap Nat)).symm
  · intro k v m hk ih
    rw [GMap.fmap_insert]
    have hk' : (m.fmap (fun _ => ())) !! k = none := by simp [hk]
    rw [show (<[k := ()]> (m.fmap (fun _ => ())) : GMap Nat Unit) =
      Std.insert (m.fmap (fun _ => ())) k () from rfl,
      show (<[k := v]> m : Pages) = Std.insert m k v from rfl]
    exact (BigSepM.bigSepM_insert (M := GMap Nat) hk').trans
      ((sep_congr .rfl ih).trans
        (BigSepM.bigSepM_insert (M := GMap Nat) (Φ := fun k (_ : List w8) => Φ k ()) hk).symm)

omit hos sem in
/-- **The page tokens of a view, allocated**: the authority knows exactly the view's page ids. -/
theorem pgToks_alloc (P : Pages) :
    ⊢ |==> ∃ γ, ghostMapAuth (GF := GF) γ 1 (P.fmap (fun _ => ())) ∗ pgToks γ P := by
  imod ghost_map_alloc (GF := GF) (P.fmap (fun _ => ())) with ⟨%γ, Ha, Ht⟩
  imodintro
  iexists γ
  iframe Ha
  unfold pgToks
  iapply (bigSepM_fmap_unit (fun k v => iprop(k ↪[γ] v)) P).1
  iexact Ht

omit hos sem in
/-- Tokens of a sub-map (a filter) of `P`. -/
theorem pgToks_filter (γ : GName) (P : Pages) (q : Nat → List w8 → Bool) :
    pgToks (GF := GF) γ P ⊢ pgToks γ (GMap.filter q P) := by
  unfold pgToks
  exact BigSepM.bigSepM_subseteq (M := GMap Nat) (GMap.map_filter_subseteq q P)

omit hos sem in
/-- **The initial writer's page tokens** (`txShape` of `wx0`, nothing extra): the root bucket has
no root node, so all its tokens are its root page's position's (`xPages` of the view). -/
theorem txShape_wx0 (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket)
    (v : View) (γ : GName) (hrn : bv.rootNode' = null) (hr : ib.root' ≠ W64 0) :
    ghostMapAuth (GF := GF) γ 1 (v.pages.fmap (fun _ => ())) ∗ pgToks γ v.pages ⊢
      txShape γ (wx0 rl t mv bv ib v) ∅ := by
  iintro ⟨Ha, Ht⟩
  unfold txShape
  iexists _
  iframe Ha
  isplitr
  · ipureintro; intro id; simp [wx0]
  isplitl [Ht]
  · simp only [wx0]
    rw [show GMap.singleton rl (brec0 bv ib) = Std.insert (∅ : GMap Loc BRec) rl (brec0 bv ib) from rfl]
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (m := (∅ : GMap Loc BRec)) (i := rl)
      (x := brec0 bv ib) (by rfl)).2
    isplitl
    · unfold bktToks
      simp only [brec0, hrn, hr, ↓reduceIte]
      unfold xPages
      iapply pgToks_filter
      iexact Ht
    · iapply BigSepM.bigSepM_empty.2; iempintro
  · unfold pgToks; rw [GMap.fmap_empty]; iapply BigSepM.bigSepM_empty.2; iempintro

omit hos sem in
/-- **A writer's names**: its agreed state, `ex`, empty handle and node registries, `done`, its
view's page tokens, and the view at its base and at the fixed key `null` (U6w, F2: `viewOf`; the
base is not `null`). -/
theorem wr_names_alloc (c : TxViewC) (x : TxX) (v : View) (hb : v.base ≠ null) :
    ⊢ |==> ∃ n : TxNames, ghostVar (GF := GF) n.v 1 (c, x) ∗ ghostVar (GF := GF) n.ex 1 () ∗
      ghostMapAuth (GF := GF) n.bk 1 (∅ : GMap Loc (GoString × Nat)) ∗
      ghostMapAuth (GF := GF) n.nl 1 (∅ : GMap Loc (Loc × Nat)) ∗
      ghostVar (GF := GF) n.done 1 false ∗
      ghostMapAuth (GF := GF) n.pg 1 (v.pages.fmap (fun _ => ())) ∗ pgToks n.pg v.pages ∗
      (v.base ↪[n.vw]□ v : IProp GF) ∗ (null ↪[n.vw]□ v : IProp GF) ∗ vwOwn (GF := GF) n.vw := by
  imod ghostVar_alloc (GF := GF) (c, x) with ⟨%γv, Hv⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γe, He⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := GoString × Nat) with ⟨%γb, Hb⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Loc × Nat) with ⟨%γn, Hn⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γd, Hd⟩
  imod pgToks_alloc (GF := GF) v.pages with ⟨%γp, Hpa, Hpt⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := View) with ⟨%γw, Hw⟩
  imod (ghost_map_insert_persist (GF := GF) v.base v (GMap.lookup_empty _)) $$ Hw with ⟨Hw, #Hf⟩
  have hnb : ((∅ : GMap Loc View).insert v.base v).lookup null = none := by
    rw [GMap.lookup_insert_ne _ _ hb]; exact GMap.lookup_empty _
  imod (ghost_map_insert_persist (GF := GF) null v hnb) $$ Hw with ⟨Hw, #Hf0⟩
  imodintro
  iexists ⟨γv, γe, γb, default, γn, γd, γp, γw⟩
  iframe
  iframe #
  unfold vwOwn
  iexists _, v
  iframe Hw
  isplitl
  · iapply (BigSepM.bigSepM_insert (M := GMap Loc) (i := null) (x := v) hnb).2
    iframe #
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (m := (∅ : GMap Loc View)) (i := v.base)
      (x := v) (by rfl)).2
    iframe #
    iapply BigSepM.bigSepM_empty.2; iempintro
  · ipureintro
    intro k u hk
    by_cases h0 : null = k
    · subst h0
      rw [GMap.lookup_insert] at hk
      cases hk
      exact ⟨rfl, fun h => absurd rfl h⟩
    · rw [GMap.lookup_insert_ne _ _ h0] at hk
      by_cases h : v.base = k
      · subst h
        rw [GMap.lookup_insert] at hk
        cases hk
        exact ⟨rfl, fun _ => rfl⟩
      · rw [GMap.lookup_insert_ne _ _ h, GMap.lookup_empty] at hk
        cases hk

end winit

end bbolt
end EtcdGrove
end Perennial
