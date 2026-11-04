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

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section winit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
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
      rfl
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
  simp only [← hrl, ↓reduceIte]
  iframe
  split <;> iempintro

end winit

end bbolt
end EtcdGrove
end Perennial
