/-
The writer's opened buckets, the heap (U6e, `notes/bbolt-proof-plan.md`): a fresh bucket object
(no nodes) added to the writer's heap, live and registered as a handle (`bktOpened`'s heap
change), and the parent's bucket cache updated (`b.buckets[name] = child`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WOpen
public import Proof.go_etcd_io.bbolt.Txn.Heap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- `X` with the new bucket `c` (record `C`), live, registered as the handle `h`. -/
def WX.addBkt (X : WX) (c : Loc) (C : BRec) (h : GoString × Nat) : WX :=
  { X with t := { X.t with bs := X.t.bs.insert c C }, liveB := X.liveB.insert c (),
           handles := X.handles.insert c h }

theorem addBkt_bs (X : WX) (c : Loc) (C : BRec) (h : GoString × Nat) (k : Loc) :
    (X.addBkt c C h).t.bs !! k = if k = c then some C else X.t.bs !! k := by
  unfold WX.addBkt
  by_cases hk : k = c
  · subst hk; simp
  · simp only [hk, ↓reduceIte]; exact GMap.lookup_insert_ne _ _ (Ne.symm hk)

theorem objsDisj_addBkt (X : WX) (c : Loc) (C : BRec) (h : GoString × Nat) (hd : objsDisj X.t)
    (hns : C.ns = ∅) : objsDisj (X.addBkt c C h).t := by
  intro b Bb hb n hn b' Bb' hb' hne
  rw [addBkt_bs] at hb hb'
  by_cases hbc : b = c
  · simp only [hbc, ↓reduceIte, Option.some.injEq] at hb
    subst hb; rw [hns] at hn; simp at hn
  · simp only [hbc, ↓reduceIte] at hb
    by_cases hbc' : b' = c
    · simp only [hbc', ↓reduceIte, Option.some.injEq] at hb'
      subst hb'; rw [hns]; rfl
    · simp only [hbc', ↓reduceIte] at hb'
      exact hd b Bb hb n hn b' Bb' hb' hne

theorem objs_addBkt (X : WX) (c : Loc) (C : BRec) (h : GoString × Nat) (hd : objsDisj X.t)
    (hns : C.ns = ∅) (hbs : X.t.bs !! c = none) : (X.addBkt c C h).t.objs = X.t.objs := by
  have hd' := objsDisj_addBkt X c C h hd hns
  apply GMap.map_eq
  intro k
  by_cases hkn : ∃ b Bb rk, X.t.bs !! b = some Bb ∧ Bb.ns !! k = some rk
  · obtain ⟨b, Bb, rk, hb, hrk⟩ := hkn
    rw [objs_node X.t b Bb k rk hd hb hrk]
    have hbc : b ≠ c := by
      intro e; subst e; rw [hbs] at hb; cases hb
    exact objs_node _ b Bb k rk hd' (by rw [addBkt_bs]; simp [hbc, hb]) hrk
  · have hno : ∀ b Bb, X.t.bs !! b = some Bb → Bb.ns !! k = none := by
      intro b Bb hb
      cases e : Bb.ns !! k with
      | none => rfl
      | some rk => exact absurd ⟨b, Bb, rk, hb, e⟩ hkn
    rw [objs_other X.t k hno, objs_other]
    · rfl
    intro b Bb hb
    rw [addBkt_bs] at hb
    by_cases hbc : b = c
    · simp only [hbc, ↓reduceIte, Option.some.injEq] at hb; subst hb; rw [hns]; rfl
    · simp only [hbc, ↓reduceIte] at hb; exact hno b Bb hb

theorem bobjs_addBkt (X : WX) (c : Loc) (C : BRec) (h : GoString × Nat) :
    (X.addBkt c C h).t.bobjs = X.t.bobjs.insert c C := by
  apply GMap.map_eq
  intro k
  by_cases hk : k = c
  · subst hk; simp [WX.addBkt, WTx.bobjs, GMap.lookup_insert]
  · have hk' : c ≠ k := Ne.symm hk
    simp [WX.addBkt, WTx.bobjs, GMap.lookup_insert_ne _ _ hk', hk']

end pure

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit hos in
/-- **A fresh bucket object added to the writer's heap** (live, a handle's). -/
theorem wtxHeap_addBkt (tx : Loc) (X : WX) (c : Loc) (C : BRec) (h : GoString × Nat)
    (hbo : X.t.bobjs !! c = none) (hns : C.ns = ∅) (htx : C.bv.tx' = tx) :
    wtxHeap (GF := GF) tx (DFrac.own 1) X ∗ objOwn X.v c (DFrac.own 1) true (.bkt C) ⊢
      wtxHeap tx (DFrac.own 1) (X.addBkt c C h) := by
  unfold wtxHeap
  iintro ⟨⟨%Hok, Hf, Hrf, Hm, Hbk⟩, Hc⟩
  have hbs : X.t.bs !! c = none := by
    unfold WTx.bobjs at hbo
    cases e : X.t.bs !! c with
    | none => rfl
    | some B => rw [GMap.lookup_union_Some_l _ _ _ _ e] at hbo; cases hbo
  have Hd := Hok.2.1
  isplitr
  · ipureintro
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := Hok
    refine ⟨k1, objsDisj_addBkt X c C h Hd hns, ?_, ?_, ?_, ?_⟩
    · intro b Bb hb
      rw [addBkt_bs] at hb
      by_cases hbc : b = c
      · simp only [hbc, ↓reduceIte, Option.some.injEq] at hb; subst hb; exact htx
      · simp only [hbc, ↓reduceIte] at hb; exact k3 b Bb hb
    · intro b Bb n rn hb hn
      rw [addBkt_bs] at hb
      by_cases hbc : b = c
      · simp only [hbc, ↓reduceIte, Option.some.injEq] at hb; subst hb; rw [hns] at hn; simp at hn
      · simp only [hbc, ↓reduceIte] at hb; exact k4 b Bb n rn hb hn
    · intro n y hn
      show ((X.addBkt c C h).t.objs !! n).isSome
      rw [objs_addBkt X c C h Hd hns hbs]
      exact k5 n y hn
    · intro b Bb hb
      rw [addBkt_bs] at hb
      by_cases hbc : b = c
      · right; subst hbc; simp [WX.addBkt]
      · simp only [hbc, ↓reduceIte] at hb
        rcases k6 b Bb hb with e | e
        · left; exact e
        · right
          show ((X.handles.insert c h) !! b).isSome
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hbc)]; exact e
  isplitl [Hf]
  · unfold txFields WX.addBkt; iexact Hf
  isplitl [Hrf]
  · iexact Hrf
  rw [objs_addBkt X c C h Hd hns hbs, bobjs_addBkt X c C h]
  have hv : (X.addBkt c C h).v = X.v := rfl
  have hlive : (X.addBkt c C h).live = X.live := rfl
  simp only [hv, hlive]
  isplitl [Hm]
  · iexact Hm
  iapply (BigSepM.bigSepM_insert (M := GMap Loc) hbo).2
  isplitl [Hc]
  · have : decide (c ∈ (X.addBkt c C h).liveB) = true := by
      simp only [WX.addBkt, GMap.mem_iff, GMap.lookup_insert, Option.isSome_some, _root_.decide_true]
    rw [this]; iexact Hc
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hbk
  intro k B hk
  have hkc : k ≠ c := by
    intro e; subst e
    rw [show Std.get? X.t.bobjs k = X.t.bobjs !! k from rfl, hbo] at hk; cases hk
  have : decide (k ∈ (X.addBkt c C h).liveB) = decide (k ∈ X.liveB) := by
    simp [WX.addBkt, GMap.mem_iff, Ne.symm hkc]
  rw [this]

/-- **The bucket cache of `bl` updated and a fresh bucket `c` opened** (`bktOpened`'s heap
change): the parent's `buckets` field and cache map out of `wtxW`, with the view's cells (to read
the name), and back with `name ↦ c` inserted and the new bucket added, live, registered as the
handle `(name, g)`, whose registry fragment is minted persistent (maintainer R's U6g item 4:
`Bucket.Bucket_w`'s post). -/
theorem wtxW_bktOpen (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hB : X.t.bs !! bl = some B) (hlB : bl ∈ X.liveB) :
    wtxW (GF := GF) K tx r m X ⊢ bl.[Bucket, go!"buckets"] ↦ B.bv.buckets' ∗
      B.bv.buckets' ↦$ B.bm ∗ viewCells wq X.v ∗
      ∀ (name : GoString) (c : Loc) (C : BRec) (g : Nat),
        bl.[Bucket, go!"buckets"] ↦ B.bv.buckets' -∗ viewCells wq X.v -∗
        B.bv.buckets' ↦$ (B.bm.insert name c) -∗ objOwn X.v c (DFrac.own 1) true (.bkt C) -∗
        (∃ f : w64, ⌜¬ float64IsNaN f⌝ ∗ c.[Bucket, go!"FillPercent"] ↦ f) -∗
        ⌜X.t.bobjs !! c = none ∧ X.handles !! c = none ∧ C.bv.tx' = tx ∧ C.ns = ∅⌝ -∗
        |==> (wtxW K tx r m ((X.setBkt bl { B with bm := B.bm.insert name c }).addBkt c C (name, g)) ∗
          c ↪[r.n.bk]□ (name, g)) := by
  unfold wtxW wtxCore
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  icases wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh with %Hok
  have htxB : B.bv.tx' = tx := Hok.2.2.1 bl B hB
  icases wtxHeap_bkt_acc tx (DFrac.own 1) X bl B hB hlB $$ Hh with ⟨Hb, Hback⟩
  isimp only [objOwn] at Hb
  icases Hb with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe H3 H9 Hcells
  iintro %name %c %C %g H3 Hcells H9 Hc ⟨%f, %Hnan, Hfp⟩ %Hfr
  obtain ⟨hbo, hhd, htx, hns⟩ := Hfr
  ihave Hh := Hback $$ %({ B with bm := B.bm.insert name c }) %htxB [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]
  · isimp only [objOwn]; iframe
  have hbo' : (X.setBkt bl { B with bm := B.bm.insert name c }).t.bobjs !! c = none := by
    rw [bobjs_setBkt]
    have hcb : bl ≠ c := by
      intro e; subst e; rw [bobjs_bkt X.t bl B hB] at hbo; cases hbo
    rw [GMap.lookup_insert_ne _ _ hcb]; exact hbo
  ihave Hh := wtxHeap_addBkt tx _ c C (name, g) hbo' hns htx $$ [Hh Hc]
  · iframe
  have hhd' : X.handles.lookup c = none := hhd
  unfold hdlAuth
  icases Hbk with ⟨Hbk, #Hhf⟩
  imod (ghost_map_insert_persist c (name, g) hhd') $$ Hbk with ⟨Hbk, #Hfr⟩
  ihave #Hhf := hdlFrags_insert r X.handles c (name, g) hhd $$ [Hhf Hfr]
  · iframe #
  imodintro
  iframe Hfr
  unfold WX.addBkt WX.setBkt
  simp only
  iframe
  isplitr
  · ipureintro; exact Hr
  iframe #
  unfold fills
  iapply (BigSepM.bigSepM_insert (M := GMap Loc) hhd).2
  iframe
  ipureintro; exact Hnan

/-- **The writer's statistics token**, with its core and registration, out of `wtxW` and back
(`Bucket.Cursor_i`'s pre). -/
theorem wtxW_stats_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ K.core ∗ reg tx K.B r ∗ statsTok r m 1 ∗
      (statsTok r m 1 -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hst; iframe Hcore; iframe Hreg
  iintro Hst
  iframe; iframe #
  ipureintro; exact Hr

/-- **A cursor's resources** out of `wtxW`: the statistics token (with the core and
registration) and the bucket's `tx` field, and back. -/
theorem wtxW_cursor_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) :
    wtxW (GF := GF) K tx r m X ⊢ K.core ∗ reg tx K.B r ∗ statsTok r m 1 ∗
      ∃ dq : DFrac, bl.[Bucket, go!"tx"] ↦{dq} tx ∗
        (statsTok r m 1 -∗ bl.[Bucket, go!"tx"] ↦{dq} tx -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  icases wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh with %Hok
  have htx : B.bv.tx' = tx := Hok.2.2.1 bl B hb
  icases wtxHeap_bkt_obj_acc tx (DFrac.own 1) X bl B (bobjs_bkt X.t bl B hb) $$ Hh with ⟨Ho, Hhb⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe Hst; iframe Hcore; iframe Hreg
  by_cases hr : bl = B.bv.tx'.[Tx, go!"root"]
  · rw [if_pos hr]
    iexists (DFrac.own 1)
    rw [htx]
    iframe H2
    iintro Hst H2
    ihave Hh := Hhb $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]
    · isimp only [objOwn]; rw [if_pos hr, htx]; iframe
    iframe; iframe #
    ipureintro; exact Hr
  · rw [if_neg hr]
    iexists DFrac.discard
    rw [htx]
    iframe H2
    iintro Hst H2
    ihave Hh := Hhb $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]
    · isimp only [objOwn]; rw [if_neg hr, htx]; iframe
    iframe; iframe #
    ipureintro; exact Hr

end heap

section heap2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **Two live slices' bytes**, out of `wtxW` (the view's cells, halved) and back. -/
theorem wtxW_src2_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (s1 s2 : GoSlice)
    (a1 a2 : Src) (b1 b2 : List w8) (h1 : a1 ≠ Src.stale) (h2 : a2 ≠ Src.stale) :
    wtxW (GF := GF) K tx r m X ∗ srcOwn X.v s1 a1 b1 ∗ srcOwn X.v s2 a2 b2 ⊢
      ∃ d1 d2 : DFrac, s1 ↦*{d1} b1 ∗ s2 ↦*{d2} b2 ∗
        (s1 ↦*{d1} b1 -∗ s2 ↦*{d2} b2 -∗ wtxW K tx r m X) := by
  iintro ⟨Hw, #Hs1, #Hs2⟩
  icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hc, Hwb⟩
  icases (viewCells_halves wq X.v).1 $$ Hc with ⟨Hc1, Hc2⟩
  icases viewCells_src_acc wq.half X.v Hbase s1 a1 b1 h1 $$ [Hc1] with ⟨%d1, Hb1, Hcb1⟩
  · iframe; iframe #
  icases viewCells_src_acc wq.half X.v Hbase s2 a2 b2 h2 $$ [Hc2] with ⟨%d2, Hb2, Hcb2⟩
  · iframe; iframe #
  iexists d1, d2
  iframe Hb1 Hb2
  iintro Hb1 Hb2
  ihave Hc1 := Hcb1 $$ Hb1
  ihave Hc2 := Hcb2 $$ Hb2
  iapply Hwb
  iapply (viewCells_halves wq X.v).2
  iframe

end heap2

end bbolt
end EtcdGrove
end Perennial
