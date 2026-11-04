/-
The writer's heap across a remap (U4, `notes/bbolt-proof-plan.md`): `wtxHeap` of `X` gives
`wtxHeap` of `X.rebase b` once `dereference` has run (`derefOK`).

`Inv/WtxHeap`'s `wtxHeap_rebase` (U0a's statement) is false: a live bucket whose `page` field is
view-backed (`pst = .view`) with an owned inline page source (`isrc = .own dq`) owns only the
fact `inViewLoc` (`pageOwn`'s `.view` case); its rebased record (`pst = .stale`, `isrc = .own dq`)
owns the page's bytes (`pageOwn`'s second case), which nothing gives. `bktOpened` never builds
such a record (a view-backed page has a view source, `WOps`), but no statement keeps it.
`wtxHeap_rebase'` adds it as a premise (`pageSrcOK`); U4 reports the fix (the premise, or
`BRec.unview` making the source of a view-backed page stale).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WtxHeap
public import Proof.go_etcd_io.bbolt.Rebalance.Objs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rebase
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A live bucket's view-backed page has a view source** (what `bktOpened` builds). -/
def pageSrcOK (X : WX) : Prop :=
  ∀ l B, X.t.objs !! l = some (.bkt B) → l ∈ X.live → B.pst = .view → B.isrc = .view

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
theorem BRec.unview_ns (B : BRec) : B.unview.ns = B.ns.fmap (fun r => { r with
    ws := (r.ws.map (fun w => { w with ks := w.ks.unview, vs := w.vs.unview })),
    ksrc := r.ksrc.unview }) := rfl

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
theorem objsDisj_rebase (X : WX) (b : Loc) (hd : objsDisj X.t) : objsDisj (X.rebase b).t := by
  intro bl B hb n hn
  simp only [WX.rebase, GMap.lookup_fmap] at hb
  obtain ⟨B0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hn0 : (B0.ns !! n).isSome := by
    rw [BRec.unview_ns, GMap.lookup_fmap] at hn; simpa using hn
  obtain ⟨h1, h2⟩ := hd bl B0 hb0 n hn0
  refine ⟨by simp [WX.rebase, h1], fun bl' B' hb' hne => ?_⟩
  simp only [WX.rebase, GMap.lookup_fmap] at hb'
  obtain ⟨B1, hb1, rfl⟩ := Option.map_eq_some_iff.1 hb'
  rw [BRec.unview_ns, GMap.lookup_fmap, h2 bl' B1 hb1 hne]; rfl

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- The rebased objects are the objects, each `unview`ed. -/
theorem objs_rebase (X : WX) (b : Loc) (hd : objsDisj X.t) :
    (X.rebase b).t.objs = X.t.objs.fmap WObj.unview := by
  have hd' := objsDisj_rebase X b hd
  apply GMap.ext; intro k
  show (X.rebase b).t.objs !! k = (X.t.objs.fmap WObj.unview) !! k
  rw [GMap.lookup_fmap]
  by_cases hk : ∃ B, X.t.bs !! k = some B
  · obtain ⟨B, hB⟩ := hk
    rw [objs_bkt X.t k B hd hB, objs_bkt _ k B.unview hd' (by simp [WX.rebase, hB])]; rfl
  · by_cases hn : ∃ bl B r, X.t.bs !! bl = some B ∧ B.ns !! k = some r
    · obtain ⟨bl, B, r, hB, hr⟩ := hn
      rw [objs_node X.t bl B k r hd hB hr, objs_node _ bl B.unview k _ hd'
        (by simp [WX.rebase, hB]) (by rw [BRec.unview_ns, GMap.lookup_fmap, hr]; rfl)]
      rfl
    · have hother : ∀ bl B, X.t.bs !! bl = some B → k ≠ bl ∧ B.ns !! k = none := by
        intro bl B hB
        refine ⟨fun e => hk ⟨B, e ▸ hB⟩, ?_⟩
        cases h : B.ns !! k with
        | none => rfl
        | some r => exact absurd ⟨bl, B, r, hB, h⟩ hn
      rw [objs_other X.t k hother, objs_other _ k ?_]
      · rfl
      · intro bl B hB
        simp only [WX.rebase, GMap.lookup_fmap] at hB
        obtain ⟨B0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hB
        obtain ⟨h1, h2⟩ := hother bl B0 hb0
        exact ⟨h1, by rw [BRec.unview_ns, GMap.lookup_fmap, h2]; rfl⟩

theorem heapOK_rebase (tx : Loc) (X : WX) (b : Loc) (h : heapOK (GF := GF) tx X) :
    heapOK (GF := GF) tx (X.rebase b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, objsDisj_rebase X b h2, ?_, ?_, ?_⟩
  · intro bl B hB
    simp only [WX.rebase, GMap.lookup_fmap] at hB
    obtain ⟨B0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hB
    exact h3 bl B0 hb0
  · intro bl B n r hB hr
    simp only [WX.rebase, GMap.lookup_fmap] at hB
    obtain ⟨B0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hB
    rw [BRec.unview_ns, GMap.lookup_fmap] at hr
    obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
    exact h4 bl B0 n r0 hb0 hr0
  · intro n y hn
    rw [objs_rebase X b h2, GMap.lookup_fmap]
    have := h5 n y hn
    revert this; cases X.t.objs !! n <;> simp

/-- A kept slice not in the view, on any view. -/
theorem srcOwn_rebase (v v' : View) (s : GoSlice) (src : Src) (bs : List w8) (h : src ≠ .view) :
    srcOwn (GF := GF) v s src bs ⊢ srcOwn v' s src.unview bs := by
  cases src with
  | view => exact absurd rfl h
  | own dq => exact .rfl
  | stale => exact .rfl

/-- A kept slice not in the view, on any view, its source kept. -/
theorem srcOwn_keep (v v' : View) (s : GoSlice) (src : Src) (bs : List w8) (h : src ≠ .view) :
    srcOwn (GF := GF) v s src bs ⊢ srcOwn v' s src bs := by
  cases src with
  | view => exact absurd rfl h
  | own dq => exact .rfl
  | stale => exact .rfl

theorem pageOwn_rebase (v v' : View) (B : BRec) (h : B.pst = .view → B.isrc = .view) :
    pageOwn (GF := GF) v B ⊢ pageOwn v' B.unview := by
  unfold pageOwn BRec.unview
  cases hp : B.pst with
  | view =>
    have hi := h hp
    simp only [hi, Src.unview, ↓reduceIte]
    iintro -
    iempintro
  | none => simp only [reduceCtorEq, ↓reduceIte]; cases B.isrc <;> exact .rfl
  | stale => simp only [reduceCtorEq, ↓reduceIte]; cases B.isrc <;> exact .rfl

private theorem fmap_bigSepM {V V' : Type} (Φ : Loc → V' → IProp GF) (f : V → V')
    (m : GMap Loc V) :
    ([∗map] k ↦ y ∈ GMap.fmap f m, Φ k y) ⊣⊢ [∗map] k ↦ x ∈ m, Φ k (f x) := by
  refine Iris.Std.LawfulFiniteMap.induction_on (M := GMap Loc) (K := Loc)
    (P := fun m => ([∗map] k ↦ y ∈ GMap.fmap f m, Φ k y) ⊣⊢ [∗map] k ↦ x ∈ m, Φ k (f x)) ?_ ?_ m
  · show ([∗map] k ↦ y ∈ GMap.fmap f (∅ : GMap Loc V), Φ k y) ⊣⊢
      [∗map] k ↦ x ∈ (∅ : GMap Loc V), Φ k (f x)
    rw [GMap.fmap_empty]
    exact ⟨BigSepM.bigSepM_empty.1.trans BigSepM.bigSepM_empty.2,
      BigSepM.bigSepM_empty.1.trans BigSepM.bigSepM_empty.2⟩
  · intro k x m hk ih
    show ([∗map] k' ↦ y ∈ GMap.fmap f (<[k := x]> m), Φ k' y) ⊣⊢
      [∗map] k' ↦ x' ∈ <[k := x]> m, Φ k' (f x')
    rw [GMap.fmap_insert]
    have hk' : GMap.fmap f m !! k = none := by
      show (m !! k).map f = none; rw [show m !! k = none from hk]; rfl
    exact (BigSepM.bigSepM_insert hk').trans ((sep_congr .rfl ih).trans
      (BigSepM.bigSepM_insert (Φ := fun k' x' => Φ k' (f x')) hk).symm)

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
theorem Src.unview_of_ne (s : Src) (h : s ≠ .view) : s.unview = s := by
  cases s <;> first | exact absurd rfl h | rfl

/-- An entry after a remap. -/
def WEntry.unview (w : WEntry) : WEntry := { w with ks := w.ks.unview, vs := w.vs.unview }

/-- A node's record after a remap. -/
def NRec.unview (r : NRec) : NRec := { r with ws := r.ws.map WEntry.unview, ksrc := r.ksrc.unview }

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
theorem WObj.unview_node (bl : Loc) (r : NRec) : WObj.unview (.node bl r) = .node bl r.unview :=
  rfl

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- A node with no view source is its own `unview`. -/
theorem nrec_unview_of (r : NRec) (hw : ∀ w ∈ r.ws, w.ks ≠ .view ∧ w.vs ≠ .view)
    (hk : r.ksrc ≠ .view) : r.unview = r := by
  have e : r.ws.map WEntry.unview = r.ws := by
    conv => rhs; rw [← List.map_id r.ws]
    apply List.map_congr_left
    intro w hw'
    obtain ⟨h1, h2⟩ := hw w hw'
    simp only [WEntry.unview, Src.unview_of_ne _ h1, Src.unview_of_ne _ h2, id]
  simp only [NRec.unview, e, Src.unview_of_ne _ hk]

/-- **An object across a remap**: a live node with no view source, a live bucket whose
view-backed page has a view source. -/
theorem objOwn_rebase (v v' : View) (l : Loc) (dq : DFrac) (live : Bool) (o : WObj)
    (hn : live = true → ∀ bl r, o = .node bl r →
      (∀ w ∈ r.ws, w.ks ≠ .view ∧ w.vs ≠ .view) ∧ r.ksrc ≠ .view)
    (hb : live = true → ∀ B, o = .bkt B → B.pst = .view → B.isrc = .view) :
    objOwn (GF := GF) v l dq live o ⊢ objOwn v' l dq live o.unview := by
  cases o with
  | bkt B =>
    simp only [objOwn, WObj.unview]
    have e1 : B.unview.bv = B.bv := rfl
    have e2 : B.unview.ib = B.ib := rfl
    have e3 : B.unview.nm = B.nm := rfl
    have e4 : B.unview.bm = B.bm := rfl
    rw [e1, e2, e3, e4]
    iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, Hp⟩
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9
    cases live with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hp
    | true =>
      simp only [↓reduceIte]
      iapply pageOwn_rebase v v' B (hb rfl B rfl)
      iexact Hp
  | node bl r =>
    cases live with
    | false => exact .rfl
    | true =>
      obtain ⟨hw, hk⟩ := hn rfl bl r rfl
      rw [WObj.unview_node, nrec_unview_of r hw hk]
      have hL : ([∗list] it;w ∈ r.ins;r.ws, wOwn (GF := GF) v true it w) ⊢
          [∗list] it;w ∈ r.ins;r.ws, wOwn v' true it w :=
        BigSepL2.bigSepL2_mono (fun {_ _ w} _ hw2 => by
          have hmem := hw w (List.mem_of_getElem? hw2)
          simp only [wOwn, ↓reduceIte]
          exact sep_mono .rfl (sep_mono (srcOwn_keep v v' _ _ _ hmem.1)
            (srcOwn_keep v v' _ _ _ hmem.2)))
      have hK : (if True ∧ r.nv.key' ≠ slice.nil then srcOwn (GF := GF) v r.nv.key' r.ksrc r.key
          else iprop(emp)) ⊢
          (if True ∧ r.nv.key' ≠ slice.nil then srcOwn v' r.nv.key' r.ksrc r.key
          else iprop(emp)) := by
        split
        · exact srcOwn_keep v v' _ _ _ hk
        · exact .rfl
      simp only [objOwn]
      exact sep_mono .rfl (sep_mono .rfl (sep_mono .rfl (sep_mono hL
        (sep_mono .rfl (sep_mono .rfl hK)))))

/-- **The writer's heap across a remap** (`Inv/WtxHeap`'s `wtxHeap_rebase` with `pageSrcOK`). -/
theorem wtxHeap_rebase' (tx : Loc) (dq : DFrac) (X : WX) (b : Loc) (hcov : derefOK X)
    (hpg : pageSrcOK X) :
    wtxHeap (GF := GF) tx dq X ⊢ wtxHeap tx dq (X.rebase b) := by
  unfold wtxHeap
  iintro ⟨%Hok, Hf, Hr, Hobjs⟩
  have ho := objs_rebase X b Hok.2.1
  isplitr
  · ipureintro; exact heapOK_rebase tx X b Hok
  have et : txFields (GF := GF) tx dq (X.rebase b) = txFields tx dq X := rfl
  rw [et]
  iframe Hf Hr
  rw [ho, show (X.rebase b).live = X.live from rfl]
  iapply (fmap_bigSepM _ _ _).2
  iapply BigSepM.bigSepM_mono (fun {l o} hlo => objOwn_rebase X.v (X.rebase b).v l dq
    (decide (l ∈ X.live)) o (fun hl bl r e => by
      have := hcov l o hlo (of_decide_eq_true hl); rw [e] at this; exact this)
    (fun hl B e => hpg l B (e ▸ hlo) (of_decide_eq_true hl)))
  iexact Hobjs

end rebase

end bbolt
end EtcdGrove
end Perennial
