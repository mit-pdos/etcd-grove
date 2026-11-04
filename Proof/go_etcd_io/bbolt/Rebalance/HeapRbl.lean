/-
The writer's heap reshaped (U8b, `node.rebalance`, `notes/bbolt-proof-plan.md`): the node objects
at a list of distinct locations and the bucket objects at another (batch 14: nodes and buckets
are separate maps) taken out of `wtxHeap` (with the transaction's fields and the root bucket's
`FillPercent`), and put back as the objects of another record `X'` that agrees with `X`
everywhere else (its objects and liveness outside the lists, its view). Every heap step of
`node.rebalance` (the start, a removal, the root collapse, a merge, a node going dead) is one.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Rebalance.RblX

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit [GooseExts] in
theorem nodup_one (a : Loc) : [a].Nodup := List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩

/-- A map with the keys of a list deleted. -/
def delL {V : Type} : List Loc → GMap Loc V → GMap Loc V
  | [], M => M
  | a :: L, M => delL L (Iris.Std.delete M a)

omit [GooseExts] in
theorem delL_lookup {V : Type} (L : List Loc) (M : GMap Loc V) (k : Loc) :
    (delL L M) !! k = if k ∈ L then none else M !! k := by
  induction L generalizing M with
  | nil => simp [delL]
  | cons a L ih =>
    simp only [delL]
    rw [ih]
    show (if k ∈ L then none else (GMap.delete a M) !! k) = _
    by_cases hk : k = a
    · subst hk; simp
    · rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
      simp [hk]

omit [GooseExts] in
theorem delL_eq {V : Type} (L : List Loc) (M M' : GMap Loc V)
    (h : ∀ k, k ∉ L → M' !! k = M !! k) : delL L M' = delL L M := by
  apply GMap.ext
  intro k
  show (delL L M') !! k = (delL L M) !! k
  rw [delL_lookup, delL_lookup]
  split
  · rfl
  · exact h k ‹_›

omit hos [GooseSemantics] [GooseInterp] go_gctx in
/-- A big separating conjunction over a map: the entries at a list of distinct keys, and the
rest. -/
theorem bigSepM_delL {V : Type} {Φ : Loc → V → IProp GF} (L : List Loc) (M : GMap Loc V)
    (os : Loc → V) (hnd : L.Nodup) (ho : ∀ l ∈ L, M !! l = some (os l)) :
    ([∗map] l ↦ o ∈ M, Φ l o) ⊣⊢ ([∗list] l ∈ L, Φ l (os l)) ∗ [∗map] l ↦ o ∈ delL L M, Φ l o := by
  induction L generalizing M with
  | nil =>
    simp only [delL]
    exact emp_sep.symm
  | cons a L ih =>
    simp only [List.nodup_cons] at hnd
    have ha : Iris.Std.get? M a = some (os a) := ho a List.mem_cons_self
    have ho' : ∀ l ∈ L, (Iris.Std.delete M a : GMap Loc V) !! l = some (os l) := by
      intro l hl
      have hne : l ≠ a := fun h => hnd.1 (h ▸ hl)
      show (GMap.delete a M) !! l = _
      rw [GMap.lookup_delete_ne _ (Ne.symm hne)]
      exact ho l (List.mem_cons_of_mem _ hl)
    refine (BigSepM.bigSepM_delete (M := GMap Loc) ha).trans ?_
    refine (sep_congr .rfl (ih _ hnd.2 ho')).trans ?_
    simp only [delL]
    exact sep_assoc.symm

omit hos in
/-- The part of a big separating conjunction outside `L`, for a record that agrees outside `L`
(entries and liveness). -/
theorem bigSepM_delL_congr {V : Type} (Φ : Bool → Loc → V → IProp GF) (L : List Loc)
    (M M' : GMap Loc V) (lv lv' : GMap Loc Unit)
    (hout : ∀ k, k ∉ L → M' !! k = M !! k ∧ (k ∈ lv' ↔ k ∈ lv)) :
    ([∗map] l ↦ o ∈ delL L M, Φ (decide (l ∈ lv)) l o) ⊢
      [∗map] l ↦ o ∈ delL L M', Φ (decide (l ∈ lv')) l o := by
  rw [delL_eq L M M' (fun k hk => (hout k hk).1)]
  iintro Hm
  iapply (BigSepM.bigSepM_mono ?_) $$ Hm
  intro k o hk
  have hk' : (delL L M) !! k = some o := hk
  rw [delL_lookup] at hk'
  split at hk'
  · cases hk'
  · rename_i hkL
    rw [show decide (k ∈ lv') = decide (k ∈ lv) from decide_eq_decide.2 (hout k hkL).2]

omit hos in
/-- **The heap reshaped**: the node objects at the distinct locations `L` and the bucket objects
at the distinct locations `Lb` (the transaction's fields and the root bucket's `FillPercent` too)
out of `X`'s heap, and back as the objects of any `X'` with `X`'s view that agrees with `X`
outside `L` and `Lb` (objects and liveness). -/
theorem wtxHeap_reshape (tx : Loc) (dq : DFrac) (X : WX) (L : List Loc) (os : Loc → WObj)
    (Lb : List Loc) (bs : Loc → BRec)
    (hnd : L.Nodup) (ho : ∀ l ∈ L, X.t.objs !! l = some (os l))
    (hndb : Lb.Nodup) (hob : ∀ l ∈ Lb, X.t.bobjs !! l = some (bs l)) :
    wtxHeap (GF := GF) tx dq X ⊢
      ([∗list] l ∈ L, objOwn X.v l dq (decide (l ∈ X.live)) (os l)) ∗
      ([∗list] l ∈ Lb, objOwn X.v l dq (decide (l ∈ X.liveB)) (.bkt (bs l))) ∗
      txFields tx dq X ∗ rootFill tx dq ∗
      (∀ (X' : WX) (os' : Loc → WObj) (bs' : Loc → BRec),
        ⌜(∀ l ∈ L, X'.t.objs !! l = some (os' l)) ∧ (∀ l ∈ Lb, X'.t.bobjs !! l = some (bs' l)) ∧
          X'.v = X.v ∧
          (∀ k, k ∉ L → X'.t.objs !! k = X.t.objs !! k ∧ (k ∈ X'.live ↔ k ∈ X.live)) ∧
          (∀ k, k ∉ Lb → X'.t.bobjs !! k = X.t.bobjs !! k ∧ (k ∈ X'.liveB ↔ k ∈ X.liveB)) ∧
          heapOK (GF := GF) tx X'⌝ -∗
        ([∗list] l ∈ L, objOwn X.v l dq (decide (l ∈ X'.live)) (os' l)) -∗
        ([∗list] l ∈ Lb, objOwn X.v l dq (decide (l ∈ X'.liveB)) (.bkt (bs' l))) -∗
        txFields tx dq X' -∗ rootFill tx dq -∗ wtxHeap tx dq X') := by
  unfold wtxHeap
  iintro ⟨%Hok, Hf, Hrf, Hm, Hbk⟩
  icases (bigSepM_delL (Φ := fun l o => objOwn (GF := GF) X.v l dq (decide (l ∈ X.live)) o)
    L X.t.objs os hnd ho).1 $$ Hm with ⟨HL, Hm⟩
  icases (bigSepM_delL (Φ := fun l B => objOwn (GF := GF) X.v l dq (decide (l ∈ X.liveB)) (.bkt B))
    Lb X.t.bobjs bs hndb hob).1 $$ Hbk with ⟨HLb, Hbk⟩
  iframe HL HLb Hf Hrf
  iintro %X' %os' %bs' %Hc HL HLb Hf Hrf
  obtain ⟨ho', hob', hv, hout, houtb, Hok'⟩ := Hc
  iframe Hf Hrf
  isplitr
  · ipureintro; exact Hok'
  rw [hv]
  isplitl [HL Hm]
  · iapply (bigSepM_delL (Φ := fun l o => objOwn (GF := GF) X.v l dq (decide (l ∈ X'.live)) o)
      L X'.t.objs os' hnd ho').2
    iframe HL
    iapply (bigSepM_delL_congr (fun b l o => objOwn (GF := GF) X.v l dq b o) L X.t.objs X'.t.objs
      X.live X'.live hout) $$ Hm
  iapply (bigSepM_delL (Φ := fun l B => objOwn (GF := GF) X.v l dq (decide (l ∈ X'.liveB)) (.bkt B))
    Lb X'.t.bobjs bs' hndb hob').2
  iframe HLb
  iapply (bigSepM_delL_congr (fun b l B => objOwn (GF := GF) X.v l dq b (.bkt B)) Lb X.t.bobjs
    X'.t.bobjs X.liveB X'.liveB houtb) $$ Hbk

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **A node in at most one bucket, kept** when the buckets stay and each bucket's nodes are
some of its nodes before. -/
theorem objsDisj_sub (T T' : WTx) (hd : objsDisj T)
    (hdom : ∀ bl, (T'.bs !! bl).isSome = (T.bs !! bl).isSome)
    (hsub : ∀ bl B B' k, T.bs !! bl = some B → T'.bs !! bl = some B' → (B'.ns !! k).isSome →
      (B.ns !! k).isSome) :
    objsDisj T' := by
  have hget : ∀ bl B', T'.bs !! bl = some B' → ∃ B, T.bs !! bl = some B := by
    intro bl B' h
    have := hdom bl; rw [h] at this
    exact Option.isSome_iff_exists.1 this.symm
  intro bl B' hb' k hk bl'' C' hc' hne
  obtain ⟨B, hb⟩ := hget bl B' hb'
  have hk0 := hsub bl B B' k hb hb' hk
  obtain ⟨C, hc⟩ := hget bl'' C' hc'
  have := hd bl B hb k hk0 bl'' C hc hne
  cases h : C'.ns !! k with
  | none => rfl
  | some _ =>
    have := hsub bl'' C C' k hc hc' (by rw [h]; rfl)
    rw [‹C.ns !! k = none›] at this; cases this

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **The nodes agree outside `L`** when the buckets' nodes (and the dead nodes) agree outside
`L`. -/
theorem objs_agree (T T' : WTx) (L : List Loc) (hd : objsDisj T) (hd' : objsDisj T')
    (hdom : ∀ bl, (T'.bs !! bl).isSome = (T.bs !! bl).isSome)
    (hns : ∀ bl B B' k, T.bs !! bl = some B → T'.bs !! bl = some B' → k ∉ L →
      B'.ns !! k = B.ns !! k)
    (hdead : ∀ k, k ∉ L → T'.dead !! k = T.dead !! k) :
    ∀ k, k ∉ L → T'.objs !! k = T.objs !! k := by
  intro k hk
  have hget : ∀ bl B, T.bs !! bl = some B → ∃ B', T'.bs !! bl = some B' := by
    intro bl B h
    have := hdom bl; rw [h] at this
    exact Option.isSome_iff_exists.1 this
  by_cases hex : ∃ bl B r, T.bs !! bl = some B ∧ B.ns !! k = some r
  · obtain ⟨bl, B, r, hb, hr⟩ := hex
    obtain ⟨B', hb'⟩ := hget bl B hb
    rw [objs_node T bl B k r hd hb hr,
      objs_node T' bl B' k r hd' hb' (by rw [hns bl B B' k hb hb' hk]; exact hr)]
  · have hno : ∀ bl B, T.bs !! bl = some B → B.ns !! k = none := by
      intro bl B hb
      cases h : B.ns !! k with
      | none => rfl
      | some r => exact absurd ⟨bl, B, r, hb, h⟩ hex
    rw [objs_other T k hno, objs_other T' k ?_]
    · simp only [WTx.deadObjs, GMap.lookup_fmap, hdead k hk]
    intro bl B' hb'
    obtain ⟨B, hb⟩ : ∃ B, T.bs !! bl = some B := by
      have := hdom bl; rw [hb'] at this
      exact Option.isSome_iff_exists.1 this.symm
    rw [hns bl B B' k hb hb' hk]; exact hno bl B hb

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **The buckets agree outside `L`** when the buckets and the dead buckets agree outside `L`. -/
theorem bobjs_agree (T T' : WTx) (L : List Loc)
    (hbs : ∀ bl, bl ∉ L → T'.bs !! bl = T.bs !! bl)
    (hdeadB : ∀ k, k ∉ L → T'.deadB !! k = T.deadB !! k) :
    ∀ k, k ∉ L → T'.bobjs !! k = T.bobjs !! k := by
  intro k hk
  simp only [WTx.bobjs, GMap.lookup_union, hbs k hk, hdeadB k hk]

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- A bucket's node under `rblX` is not its own parent (`rblAcyc`). -/
theorem parentNe_of_rblX (X : WX) (fl : FLPg) (dbl : Loc) (dfc : Option Loc) (hI : rblX X fl dbl dfc) :
    ∀ bl B n r, X.t.bs !! bl = some B → B.ns !! n = some r → r.nv.parent' ≠ n := by
  intro bl B n r hb hr he
  obtain ⟨-, -, ⟨ht, hh⟩, -⟩ := (hI.2.1 bl B hb).1
  have hpn : r.nv.parent' ≠ null := by
    intro h0
    have hc := (hI.2.1 bl B hb).1.1
    have hnm := (hc.2.2.2.2.2.2.2.1 n r hr).2.2.2.2.2.2.2.1
    exact (hc.2.2.2.2.1 _ _ hnm).1 (he.symm.trans h0)
  have := hh n r hr hpn; rw [he] at this; omega

omit hos [GooseSemantics] in
/-- The heap's facts for a reshaped record: the root, a node in at most one bucket, the buckets'
`tx` fields, no node its own parent, the registry's nodes still objects, and every bucket the
root or a handle's (the buckets some of `X`'s, the handles kept). -/
theorem heapOK_of (tx : Loc) (X X' : WX) (hok : heapOK (GF := GF) tx X) (hrl : X'.rl = X.rl)
    (hd : objsDisj X'.t)
    (htx : ∀ bl B', X'.t.bs !! bl = some B' → ∃ B, X.t.bs !! bl = some B ∧ B'.bv.tx' = B.bv.tx')
    (hpar : ∀ bl B n r, X'.t.bs !! bl = some B → B.ns !! n = some r → r.nv.parent' ≠ n)
    (hnl : X'.nloc = X.nloc)
    (hobj : ∀ k, (X.t.objs !! k).isSome → (X'.t.objs !! k).isSome)
    (hh : X'.handles = X.handles) :
    heapOK (GF := GF) tx X' := by
  obtain ⟨h1, -, h3, -, h5, h6⟩ := hok
  refine ⟨hrl.trans h1, hd, ?_, hpar, ?_, ?_⟩
  · intro bl B' hb'
    obtain ⟨B, hb, he⟩ := htx bl B' hb'
    rw [he]; exact h3 bl B hb
  · intro k y hk
    rw [hnl] at hk
    exact hobj k (h5 k y hk)
  · intro bl B' hb'
    obtain ⟨B, hb, -⟩ := htx bl B' hb'
    rw [hrl, hh]; exact h6 bl B hb

omit hos in
/-- The transaction's fields depend only on its struct, meta copy and page cache. -/
theorem txFields_congr (tx : Loc) (dq : DFrac) (X X' : WX) (h1 : X'.t.t = X.t.t)
    (h2 : X'.t.mv = X.t.mv) (h3 : X'.t.pm = X.t.pm) (h4 : X'.t.bufs = X.t.bufs) :
    txFields (GF := GF) tx dq X' = txFields tx dq X := by
  unfold txFields; rw [h1, h2, h3, h4]

omit hos in
/-- A bucket's object does not depend on its nodes. -/
theorem objOwn_bkt_ns (v : View) (l : Loc) (dq : DFrac) (b : Bool) (B : BRec)
    (ns : GMap Loc NRec) :
    objOwn (GF := GF) v l dq b (.bkt { B with ns := ns }) = objOwn v l dq b (.bkt B) := by
  simp only [objOwn, pageOwn]

omit hos in
/-- A bucket's object does not depend on its nodes, nor its node cache's contents but through
`nm` (the record's other fields kept). -/
theorem objOwn_bkt_eq (v : View) (l : Loc) (dq : DFrac) (b : Bool) (B B' : BRec)
    (h1 : B'.bv = B.bv) (h2 : B'.ib = B.ib) (h3 : B'.nm = B.nm) (h4 : B'.bm = B.bm)
    (h5 : B'.ipg = B.ipg) (h6 : B'.isrc = B.isrc) (h7 : B'.pst = B.pst) :
    objOwn (GF := GF) v l dq b (.bkt B') = objOwn v l dq b (.bkt B) := by
  simp only [objOwn, pageOwn, h1, h2, h3, h4, h5, h6, h7]

omit hos in
/-- **A bucket's record changed and some of its nodes no longer live** (the root collapse: the
child gives its slices to the root before `free`): some of its nodes (`Ls`, their records `f`
before) and its object out; back with any new record `B'` with the same nodes but `Ls`' (their
records `f'`), its `tx` field kept, no node of `Ls` its own parent, and the live set `lv'`
agreeing with `X`'s outside `Ls`. -/
theorem wtxHeap_setBkt_live_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec)
    (Ls : List Loc) (f : Loc → NRec) (hb : X.t.bs !! bl = some B) (hnd : Ls.Nodup)
    (hf : ∀ l ∈ Ls, B.ns !! l = some (f l)) :
    wtxHeap (GF := GF) tx dq X ⊢
      ([∗list] l ∈ Ls, objOwn X.v l dq (decide (l ∈ X.live)) (.node bl (f l))) ∗
      objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B) ∗ txFields tx dq X ∗ rootFill tx dq ∗
      (∀ (B' : BRec) (f' : Loc → NRec) (lv' : GMap Loc Unit), ⌜(∀ l ∈ Ls, B'.ns !! l = some (f' l)) ∧
          (∀ l, l ∉ Ls → B'.ns !! l = B.ns !! l) ∧ B'.bv.tx' = B.bv.tx' ∧
          (∀ l ∈ Ls, (f' l).nv.parent' ≠ l) ∧ (∀ k, k ∉ Ls → (k ∈ lv' ↔ k ∈ X.live))⌝ -∗
        ([∗list] l ∈ Ls, objOwn X.v l dq (decide (l ∈ lv')) (.node bl (f' l))) -∗
        objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B') -∗ txFields tx dq X -∗ rootFill tx dq -∗
        wtxHeap tx dq { X.setBkt bl B' with live := lv' }) := by
  iintro H
  ihave %Hok := wtxHeap_heapOK tx dq X $$ H
  have Hd := Hok.2.1
  have Hob := bobjs_bkt X.t bl B hb
  let os : Loc → WObj := fun l => .node bl (f l)
  have ho : ∀ l ∈ Ls, X.t.objs !! l = some (os l) := by
    intro l hl
    exact objs_node X.t bl B l (f l) Hd hb (hf l hl)
  icases wtxHeap_reshape tx dq X Ls os [bl] (fun _ => B) hnd ho (nodup_one bl)
    (by intro l hl; rw [List.mem_singleton.1 hl]; exact Hob) $$ H
    with ⟨HL, ⟨Hb, -⟩, Hf, Hrf, Hback⟩
  iframe Hf Hrf HL Hb
  iintro %B' %f' %lv' %Hc HL Hb Hf Hrf
  obtain ⟨hf', hout, htx, hpar, hlv⟩ := Hc
  let os' : Loc → WObj := fun l => .node bl (f' l)
  let T' : WTx := { X.t with bs := X.t.bs.insert bl B' }
  have hbs' : ∀ c, T'.bs !! c = if c = bl then some B' else X.t.bs !! c := by
    intro c
    show (X.t.bs.insert bl B') !! c = _
    split
    · rename_i h; subst h; exact GMap.lookup_insert _ _ _
    · exact GMap.lookup_insert_ne _ _ (Ne.symm ‹_›)
  have hdom : ∀ c, (T'.bs !! c).isSome = (X.t.bs !! c).isSome := by
    intro c; rw [hbs']; split
    · rename_i h; subst h; rw [hb]; rfl
    · rfl
  have hnsd : ∀ k, (B'.ns !! k).isSome = (B.ns !! k).isSome := by
    intro k
    by_cases hk : k ∈ Ls
    · rw [hf k hk, hf' k hk]; rfl
    · rw [hout k hk]
  have hsub : ∀ c C C' k, X.t.bs !! c = some C → T'.bs !! c = some C' → (C'.ns !! k).isSome →
      (C.ns !! k).isSome := by
    intro c C C' k hc hc' hk
    rw [hbs'] at hc'
    split at hc'
    · rename_i h; subst h; cases hc'; rw [hb] at hc; cases hc; rw [← hnsd]; exact hk
    · rw [hc] at hc'; cases hc'; exact hk
  have Hd' : objsDisj T' := objsDisj_sub X.t T' Hd hdom hsub
  have hagree := objs_agree X.t T' Ls Hd Hd' hdom
    (fun c C C' k hc hc' hk => by
      rw [hbs'] at hc'
      split at hc'
      · rename_i h; subst h; cases hc'; rw [hb] at hc; cases hc
        exact hout k hk
      · rw [hc] at hc'; cases hc'; rfl)
    (fun k _ => rfl)
  have hagreeB := bobjs_agree X.t T' [bl]
    (fun c hc => by rw [hbs', if_neg]; intro h; exact hc (by rw [h]; exact List.mem_singleton_self _))
    (fun k _ => rfl)
  have ho' : ∀ l ∈ Ls, T'.objs !! l = some (os' l) := by
    intro l hl
    exact objs_node T' bl B' l (f' l) Hd' (by rw [hbs', if_pos rfl]) (hf' l hl)
  rw [show ({ X.setBkt bl B' with live := lv' } : WX) = ({ X with t := T', live := lv' } : WX)
    from rfl]
  iapply Hback $$ %({ X with t := T', live := lv' } : WX) %os' %(fun _ => B') [] [HL] [Hb] [Hf] [Hrf]
  · ipureintro
    refine ⟨ho', ?_, rfl, fun k hk => ⟨hagree k hk, hlv k hk⟩, fun k hk => ⟨hagreeB k hk, Iff.rfl⟩, ?_⟩
    · intro l hl; rw [List.mem_singleton.1 hl]
      exact bobjs_bkt T' bl B' (by rw [hbs', if_pos rfl])
    refine heapOK_of tx X _ Hok rfl Hd' ?_ ?_ rfl ?_ rfl
    · intro c C' hc'
      change T'.bs !! c = some C' at hc'
      rw [hbs'] at hc'
      split at hc'
      · rename_i h; subst h; cases hc'; exact ⟨B, hb, htx⟩
      · exact ⟨C', hc', rfl⟩
    · intro c C' k rk hc' hk
      change T'.bs !! c = some C' at hc'
      rw [hbs'] at hc'
      split at hc'
      · rename_i h; subst h; cases hc'
        by_cases hkL : k ∈ Ls
        · rw [hf' k hkL] at hk; cases hk; exact hpar k hkL
        · rw [hout k hkL] at hk; exact Hok.2.2.2.1 c B k rk hb hk
      · exact Hok.2.2.2.1 c C' k rk hc' hk
    · intro k hk
      by_cases hkL : k ∈ Ls
      · show (T'.objs !! k).isSome; rw [ho' k hkL]; rfl
      · show (T'.objs !! k).isSome; rw [hagree k hkL]; exact hk
  · iexact HL
  · iapply BigSepL.bigSepL_singleton.2; iexact Hb
  · rw [txFields_congr tx dq ({ X with t := T', live := lv' } : WX) X rfl rfl rfl rfl]; iexact Hf
  · iexact Hrf

omit hos in
/-- **A bucket's record changed** (`X.setBkt`): some of its nodes (`Ls`, their records `f`
before) and its object out; back with any new record `B'` with the same nodes but `Ls`' (their
records `f'`), its `tx` field kept, no node of `Ls` its own parent. -/
theorem wtxHeap_setBkt_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec)
    (Ls : List Loc) (f : Loc → NRec) (hb : X.t.bs !! bl = some B) (hnd : Ls.Nodup)
    (hf : ∀ l ∈ Ls, B.ns !! l = some (f l)) :
    wtxHeap (GF := GF) tx dq X ⊢
      ([∗list] l ∈ Ls, objOwn X.v l dq (decide (l ∈ X.live)) (.node bl (f l))) ∗
      objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B) ∗ txFields tx dq X ∗ rootFill tx dq ∗
      (∀ (B' : BRec) (f' : Loc → NRec), ⌜(∀ l ∈ Ls, B'.ns !! l = some (f' l)) ∧
          (∀ l, l ∉ Ls → B'.ns !! l = B.ns !! l) ∧ B'.bv.tx' = B.bv.tx' ∧
          (∀ l ∈ Ls, (f' l).nv.parent' ≠ l)⌝ -∗
        ([∗list] l ∈ Ls, objOwn X.v l dq (decide (l ∈ X.live)) (.node bl (f' l))) -∗
        objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B') -∗ txFields tx dq X -∗ rootFill tx dq -∗
        wtxHeap tx dq (X.setBkt bl B')) := by
  iintro H
  icases wtxHeap_setBkt_live_acc tx dq X bl B Ls f hb hnd hf $$ H with ⟨HL, Hb, Hf, Hrf, Hback⟩
  iframe HL Hb Hf Hrf
  iintro %B' %f' %Hc HL Hb Hf Hrf
  obtain ⟨hf', hout, htx, hpar⟩ := Hc
  have e : ({ X.setBkt bl B' with live := X.live } : WX) = X.setBkt bl B' := rfl
  rw [← e]
  iapply Hback $$ %B' %f' %X.live [] [HL] [Hb] [Hf] [Hrf]
  · ipureintro; exact ⟨hf', hout, htx, hpar, fun _ _ => Iff.rfl⟩
  · iexact HL
  · iexact Hb
  · iexact Hf
  · iexact Hrf

omit hos in
/-- **A node's record changed** (`X.setNode`), its bucket's object, the transaction's fields and
the root's `FillPercent` out too. -/
theorem wtxHeap_setNode_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec) (n : Loc)
    (r : NRec) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v n dq (decide (n ∈ X.live)) (.node bl r) ∗
      objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B) ∗ txFields tx dq X ∗ rootFill tx dq ∗
      (∀ r', ⌜r'.nv.parent' ≠ n⌝ -∗ objOwn X.v n dq (decide (n ∈ X.live)) (.node bl r') -∗
        objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B) -∗ txFields tx dq X -∗ rootFill tx dq -∗
        wtxHeap tx dq (X.setNode bl n r')) := by
  iintro H
  icases wtxHeap_setBkt_acc tx dq X bl B [n] (fun _ => r) hb (nodup_one n)
    (by intro l hl; rw [List.mem_singleton.1 hl]; exact hr) $$ H with ⟨⟨Hn, -⟩, Hb, Hf, Hrf, Hback⟩
  iframe Hn Hb Hf Hrf
  iintro %r' %Hpar Hn Hb Hf Hrf
  rw [setNode_eq X bl n B r' hb]
  have e : ({ X with t := X.t.setNodeT bl n B r' } : WX) =
      X.setBkt bl { B with ns := B.ns.insert n r' } := rfl
  rw [e]
  iapply Hback $$ %{ B with ns := B.ns.insert n r' } %(fun _ => r') [] [Hn] [Hb] [Hf] [Hrf]
  · ipureintro
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro l hl; rw [List.mem_singleton.1 hl]; simp
    · intro l hl
      have hne : l ≠ n := fun h => hl (by rw [h]; exact List.mem_singleton_self _)
      show (B.ns.insert n r') !! l = B.ns !! l
      exact GMap.lookup_insert_ne _ _ (Ne.symm hne)
    · intro l hl; rw [List.mem_singleton.1 hl]; exact Hpar
  · iapply BigSepL.bigSepL_singleton.2; iexact Hn
  · rw [objOwn_bkt_eq _ _ _ _ B { B with ns := B.ns.insert n r' } rfl rfl rfl rfl rfl rfl rfl]
    iexact Hb
  · iexact Hf
  · iexact Hrf

end heap

end bbolt
end EtcdGrove
end Perennial
