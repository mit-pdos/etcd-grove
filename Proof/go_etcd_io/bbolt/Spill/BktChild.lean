/-
`Bucket.spill` for a nested bucket (U9g, `notes/bbolt-proof-plan.md`): `Spill/BktSpec`'s
`Bucket.spill.specC`, over `node.spill.spec'` (top case), `node.root`, `Meta.Pgid` and
`InBucket.SetRootPage`. The loop over `b.buckets` runs no iteration (`B.bm = ∅`).

The data clauses: the written tree's leaf elements are the unspilled tree's (`node.spill.spec'`'s
top case), which `bkPre` relates to the bucket's entries and says plain.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktSpec
public import Proof.go_etcd_io.bbolt.Spill.DerefHeap
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Spill.BktLoopFreeNC
public import Proof.go_etcd_io.bbolt.Rebalance.HeapRbl
public import Proof.go_etcd_io.bbolt.Read.BktOK
public import Spec.go_etcd_io.bbolt.node__root
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__SetRootPage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- **A written tree of plain elements holds plain entries** (`plainTree`): its leaves are
well-formed leaf pages (`sTree`), so their elements' key and value sizes are the lengths of
their bytes. -/
theorem plainTree_of_els {P : Pages} {hwm root : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} {E : List El} (hs : sTree P hwm root lo hi h S) (hE : treeEls P root = E)
    (hpl : plainEls E) : plainTree P root := by
  intro pg hpg j hj
  obtain ⟨-, -, -, -, -, hfl, hpt, -⟩ :=
    leavesF_page P hwm _ root lo hi hs.wf hs.keys pg hpg
  have hmem : (leafFlags pg j, leafKey pg j, leafValue pg j) ∈ E := by
    rw [← hE]; unfold treeEls
    exact List.mem_flatMap.2 ⟨pg, hpg, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩
  obtain ⟨h1, h2, h3⟩ := hpl _ hmem
  cases hpt with
  | branch _ _ hb _ _ => rw [hfl] at hb; cases hb
  | leaf _ _ _ hwf _ =>
    have hb := (hwf.2.2.1 j hj).1
    have hk : (leafKey pg j).length = leafKsize pg j := by
      unfold leafKey bytesAt; simp only [List.length_take, List.length_drop]; have := hwf.1; omega
    have hv : (leafValue pg j).length = leafVsize pg j := by
      unfold leafValue bytesAt; simp only [List.length_take, List.length_drop]; have := hwf.1; omega
    simp only at h1 h2 h3
    exact ⟨h1, by omega, by omega⟩

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem bk_node_of_bs {X : WX} {bl n : Loc} {rn : NRec} (h : X.node bl n = some rn) :
    ∃ B, X.t.bs !! bl = some B ∧ B.ns !! n = some rn := by
  unfold WX.node at h
  cases hb : X.t.bs !! bl with
  | none => rw [hb] at h; cases h
  | some B => rw [hb] at h; exact ⟨B, rfl, h⟩

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- The top of an unspilled tree is not spilled. -/
theorem uTree_top_unspilled {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc} {lo hi h F D N E}
    {rn : NRec} (hu : uTree X bl P hwm n lo hi h F D N E) (hr : X.node bl n = some rn) :
    rn.nv.spilled' = false := by
  cases hu with
  | leaf _ r _ _ _ hr' hun => rw [hr] at hr'; cases hr'; exact hun.2.2.1
  | branch _ r _ _ _ _ hr' hun => rw [hr] at hr'; cases hr'; exact hun.2.2.1

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem setBkt_bs_eq (X : WX) (bl bl' : Loc) (B' : BRec) :
    (X.setBkt bl B').t.bs !! bl' = if bl' = bl then some B' else X.t.bs !! bl' := by
  unfold WX.setBkt
  by_cases h : bl' = bl
  · subst h; simp only [if_pos rfl]; exact GMap.lookup_insert _ _ _
  · simp only [if_neg h]; exact GMap.lookup_insert_ne _ _ (Ne.symm h)

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- A bucket of `X` after `bkRooted`: the same nodes and caches, the same record if another. -/
theorem setBkt_bkRooted_bs {X : WX} {bl rt : Loc} {B : BRec} {pg : w64}
    (hB : X.t.bs !! bl = some B) {bl' : Loc} {B' : BRec}
    (h : (X.setBkt bl (bkRooted B rt pg)).t.bs !! bl' = some B') :
    ∃ B0, X.t.bs !! bl' = some B0 ∧ B'.ns = B0.ns ∧ B'.bm = B0.bm ∧ (bl' ≠ bl → B' = B0) := by
  rw [setBkt_bs_eq] at h
  by_cases e : bl' = bl
  · rw [if_pos e] at h; cases h; subst e; exact ⟨B, hB, rfl, rfl, fun h => absurd rfl h⟩
  · rw [if_neg e] at h; exact ⟨B', h, rfl, rfl, fun _ => rfl⟩

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- **The spill's global state after `b.rootNode = root; SetRootPage`** (the root `rt` of the old
root node, without a parent, live). -/
theorem spG_bkRooted {X : WX} {txid : w64} {ml : Nat} {fl : FLPg} {bl rt : Loc} {B : BRec}
    {rr : NRec} (pg : w64) (hG : spG X txid ml fl) (hB : X.t.bs !! bl = some B) (hr : B.ns !! rt = some rr)
    (hp : rr.nv.parent' = null) (hl : rt ∈ X.live) (hroot : nodeRootIn B B.bv.rootNode' rt) :
    spG (X.setBkt bl (bkRooted B rt pg)) txid ml fl := by
  obtain ⟨h1, h2, ⟨d1, d2, d3, d4, d5⟩, hf, ⟨r1, r2⟩, h6, h7, h8⟩ := hG
  have hrootN : nodeRootIn (bkRooted B rt pg) rt rt := nodeRootIn.top rt rr hr hp
  have hdesc : ∀ a d, descIn B a d → descIn (bkRooted B rt pg) a d := by
    intro a d h
    induction h with
    | self n => exact .self n
    | child n c d r hr hc _ ih => exact .child n c d r hr hc ih
  have hsome : ∀ c, (X.t.bs !! c).isSome → ((X.setBkt bl (bkRooted B rt pg)).t.bs !! c).isSome := by
    intro c hc; rw [setBkt_bs_eq]; split
    · rfl
    · exact hc
  refine ⟨h1, h2, ⟨?_, ?_, ?_, ?_, d5⟩, ?_, ⟨?_, ?_⟩, h6, h7, h8⟩
  · intro bl' B' l r hB' hr' hl'
    obtain ⟨B0, hB0, hns, -, -⟩ := setBkt_bkRooted_bs hB hB'
    rw [hns] at hr'
    obtain ⟨a, b, c, dd⟩ := d1 bl' B0 l r hB0 hr' hl'
    exact ⟨a, b, c, fun c hc => ⟨(dd c hc).1, by rw [hns]; exact (dd c hc).2⟩⟩
  · intro bl' B' hB' hlb
    obtain ⟨B0, hB0, -, hbm, hne⟩ := setBkt_bkRooted_bs hB hB'
    by_cases e : bl' = bl
    · subst e
      rw [hB] at hB0; cases hB0
      rw [setBkt_bs_eq, if_pos rfl] at hB'; cases hB'
      exact ⟨fun k c hk => ⟨((d2 bl' B hB hlb).1 k c hk).1, hsome c ((d2 bl' B hB hlb).1 k c hk).2⟩,
        fun _ => ⟨rt, hrootN, hl⟩⟩
    · rw [hne e]
      exact ⟨fun k c hk => ⟨((d2 bl' B0 hB0 hlb).1 k c hk).1, hsome c ((d2 bl' B0 hB0 hlb).1 k c hk).2⟩,
        (d2 bl' B0 hB0 hlb).2⟩
  · intro bl' B' hB'
    obtain ⟨B0, hB0, hns, -, -⟩ := setBkt_bkRooted_bs hB hB'
    exact ⟨(d3 bl' B0 hB0).1, by rw [hns]; exact (d3 bl' B0 hB0).2⟩
  · show ((X.setBkt bl (bkRooted B rt pg)).t.bs !! X.rl).isSome
    rw [setBkt_bs_eq]; split
    · rfl
    · exact d4
  · intro bl' B' l r hB' hr' hl'
    obtain ⟨B0, hB0, hns, -, -⟩ := setBkt_bkRooted_bs hB hB'
    rw [hns] at hr'
    exact hf bl' B0 l r hB0 hr' hl'
  · intro bl' B' hB' hlb
    obtain ⟨B0, hB0, -, -, -⟩ := setBkt_bkRooted_bs hB hB'
    have hrc := r1 bl' B0 hB0 hlb
    clear hB' hB0 hlb
    induction hrc with
    | root => exact .root
    | child b c B2 n hB2 hn _ ih =>
      by_cases e : b = bl
      · subst e; rw [hB] at hB2; cases hB2
        exact .child b c (bkRooted B rt pg) n (by rw [setBkt_bs_eq]; simp) hn ih
      · exact .child b c B2 n (by rw [setBkt_bs_eq, if_neg e]; exact hB2) hn ih
  · intro bl' B' l r hB' hr' hl'
    obtain ⟨B0, hB0, hns, -, hne⟩ := setBkt_bkRooted_bs hB hB'
    by_cases e : bl' = bl
    · subst e
      rw [hB] at hB0; cases hB0
      rw [setBkt_bs_eq, if_pos rfl] at hB'; cases hB'
      obtain ⟨rt0, h0, hd⟩ := r2 bl' B l r hB hr' hl'
      rw [nodeRootIn_unique h0 hroot] at hd
      exact ⟨rt, hrootN, hdesc _ _ hd⟩
    · rw [hne e]; rw [hne e] at hr'; exact r2 bl' B0 l r hB0 hr' hl'

/-- **The writer database's slot facts** `spPre` takes (U9x3): the free ids cover no tree slot of
`w.C` (`wdbOK`, `freeNoCov_of_wdbOK`), the tree's slots are below the mark (`bkPre`'s clause). -/
theorem bk_slotFacts {X : WX} {w : WDb} {bl : Loc} {B : BRec} {O : List Nat} {h : Nat}
    {F D : List Nat} {N : List Loc} (hpre : bkPre X w bl B O h F D N) (hok : wdbOK w) :
    (∀ y ∈ w.fl.free, ¬ coversSlot w.C.pages y.toNat) ∧
      (∀ s ∈ treeSlots w.C, s < X.t.mv.pgid'.toNat) :=
  ⟨freeNoCov_of_wdbOK hok, hpre.2.2.2.2.1⟩

/-- **The nested bucket's parent pointers** `spPre` takes (U9w3): `bkPre`'s, with a root node;
without one, no node of the bucket is live (`liveReach`: a live node descends from the root node's
root, and `null` is no node). -/
theorem bk_parOK {X : WX} {w : WDb} {bl : Loc} {B : BRec} {O : List Nat} {h : Nat}
    {F D : List Nat} {N : List Loc} (hpre : bkPre X w bl B O h F D N) : parOK X bl := by
  obtain ⟨hB, -, -, hG, -, hcase⟩ := hpre
  rcases hcase with hnull | ⟨-, -, -, -, -, -, -, -, -, hpo⟩
  · -- no root node: no live node (a live node descends from the root node's root)
    intro m rm hm hl
    obtain ⟨B', hB', hr⟩ := bk_node_of_bs hm
    rw [hB] at hB'; cases hB'
    obtain ⟨rt, hrt, -⟩ := hG.2.2.2.2.1.2 bl B m rm hB hr hl
    rw [hnull] at hrt
    have hnn := (hG.2.2.1.2.2.1 bl B hB).2
    cases hrt with
    | top _ r h0 _ => rw [hnn] at h0; cases h0
    | up _ _ r h0 _ _ => rw [hnn] at h0; cases h0
  · exact hpo

omit package_sem in
/-- `wdbW`'s `wdbOK`. -/
theorem wdbW_okB (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ wdbW K tx v w ∗ ⌜wdbOK w⌝ := by
  unfold wdbW
  iintro ⟨H, %Hp⟩
  isplitl [H]
  · isplitl [H]
    · iexact H
    · ipureintro; exact Hp
  · ipureintro; exact Hp.1

theorem Bucket.spill.wp_child (hNS : node.spill.spec' (GF := GF) (hG := hG))
    (hRoot : node.root.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hSRP : internal.common.InBucket.SetRootPage.spec (GF := GF) (hG := hG)) :
    Bucket.spill.specC (GF := GF) (hG := hG) := by
  intro K tx r m X w bl B O h F D N Hpre
  iintro %Φ ⟨Hw, Hdb⟩ HΦ
  have Hpre0 := Hpre
  obtain ⟨HB, Hlive, Hbm0, HG, -, Hcase⟩ := Hpre
  icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
  icases wtxHeap_bkt_peek tx _ X bl B HB Hlive $$ Hh with ⟨Ho, Hhb⟩
  unfold objOwn
  icases Ho with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
  wp_method_call
  wp_call
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun (_keys : List GoString) (_i : Nat) (m' : GMap GoString Loc) =>
      iprop(⌜m' = B.bm⌝ : IProp GF)) $$ Hbm
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  have Hk0 : keys = [] := by
    cases keys with
    | nil => rfl
    | cons k _ =>
      have := (Hkset k).1 (by simp)
      rw [Hbm0] at this; simp at this
  subst Hk0
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hkey, -⟩ -
    simp at Hkey
  isplitr
  · imodintro
    iintro %i %key %m' ⟨%Hkey, -⟩ -
    simp at Hkey
  iintro %m' %Hm' Hbm
  subst Hm'
  try wp_auto
  rcases Hcase with Hnull | ⟨rn, E, Hrn0, Hpar, Hu, Hsi, Hsf, HEd, HEp, -⟩
  · rw [decide_eq_true Hnull]
    try wp_auto
    ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
    · dsimp only; iframe
    ihave Hw := Hclose $$ %X [] Hh Hv Hst
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    iapply HΦ
    unfold bkPost
    ileft
    isplitr
    · ipureintro; rfl
    iexists X, w, []
    iframe
    ipureintro
    exact ⟨⟨rfl, rfl, rfl, HG, HG.2.1, fun s hs => hs, fun x hx => absurd rfl hx, fun F _ h => h, id⟩,
      Or.inl ⟨Hnull, rfl, rfl⟩⟩
  obtain ⟨B0, HB0, Hrn1⟩ := bk_node_of_bs Hrn0
  rw [HB] at HB0; cases HB0
  have HrnN : B.bv.rootNode' ≠ null := by
    intro h0; rw [h0, (HG.2.2.1.2.2.1 bl B HB).2] at Hrn1; cases Hrn1
  rw [decide_eq_false HrnN]
  try wp_auto
  ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
  · dsimp only; iframe
  ihave Hw := Hclose $$ %X [] Hh Hv Hst
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  icases wdbW_ofC K tx X.v w $$ Hdb with ⟨Hdb, %Hvc⟩
  icases wdbW_okB K tx X.v w $$ Hdb with ⟨Hdb, %Hok⟩
  have Hsp : spPre X w bl B.bv.rootNode' rn O none none h F D N E .top :=
    ⟨Hrn0, HG, Or.inr ⟨Hu, ⟨Hpar, B, HB, nodeRootIn.top _ rn Hrn1 Hpar, fun x hx hne => by
      cases hx with
      | self => exact absurd rfl hne
      | up _ _ _ _ _ hne' _ => exact absurd rfl hne'⟩, Hsi, Hsf, Hvc,
      (bk_slotFacts Hpre0 Hok).1, (bk_slotFacts Hpre0 Hok).2, bk_parOK Hpre0⟩⟩
  wp_apply hNS K tx r m X w bl B.bv.rootNode' rn O none none h F D N E .top Hsp $$ [Hw Hdb]
    as %err Hpost
  · iframe
  try wp_auto
  unfold spPost
  icases Hpost with (⟨%he, %X1, %w1, %st, Hw, Hdb, %Hdone⟩ | ⟨%hne, #HeOk, %X1, %w1, %st, %Hst1, Hcase⟩)
  · subst he
    try wp_auto
    obtain ⟨Hstep, Hc⟩ := Hdone
    rcases Hc with ⟨Hsp1, -, -⟩ | ⟨-, T, D', Hfr, -, Hsi', HD1, HD2, -, -, rt, rr, S, h', Hrt, Hrtl,
      Hrsp, Hrpar, ⟨B1, HB1, Hroot⟩, HsT, HD', HEls⟩
    · rw [uTree_top_unspilled Hu Hrn0] at Hsp1; cases Hsp1
    obtain ⟨B2, HB2, Hsim, -⟩ := Hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.1 B HB
    rw [HB1] at HB2; cases HB2
    have Hlive1 : bl ∈ X1.liveB := by rw [Hfr.2.2.2.1]; exact Hlive
    have Hbv : B1.bv = B.bv := Hsim.1
    rw [← Hbv] at Hroot
    icases wtxW_open K tx r m X1 $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hclose⟩
    icases wtxHeap_bkt_peek tx _ X1 bl B1 HB1 Hlive1 $$ Hh with ⟨Ho, Hhb⟩
    unfold objOwn
    icases Ho with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
    try wp_auto
    ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
    · dsimp only; iframe
    wp_apply hRoot tx (DFrac.own 1) X1 bl B1 B1.bv.rootNode' rt HB1 Hroot $$ [Hh] as Hh
    · iframe
    try wp_auto
    obtain ⟨B3, HB3, Hrr⟩ := bk_node_of_bs Hrt
    rw [HB1] at HB3; cases HB3
    ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X1 $$ Hh
    have hbtx : B1.bv.tx' = tx := Hok.2.2.1 bl B1 HB1
    icases wtxHeap_setBkt_acc tx (DFrac.own 1) X1 bl B1 [rt] (fun _ => rr) HB1 (nodup_one rt)
      (by intro l hl; rw [List.mem_singleton.1 hl]; exact Hrr) $$ Hh
      with ⟨⟨Hn, -⟩, Hbo, Hf, Hrf, Hback⟩
    rw [decide_eq_true Hrtl, decide_eq_true Hlive1]
    icases objOwn_node_ptr_acc X1.v rt (DFrac.own 1) true bl rr $$ Hn with ⟨Hn, Hnback⟩
    unfold objOwn
    icases Hbo with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    ihave Htxf : (∃ dqb : DFrac, bl.[Bucket, go!"tx"] ↦{dqb} tx ∗
        (bl.[Bucket, go!"tx"] ↦{dqb} tx -∗
          if bl = B1.bv.tx'.[Tx, go!"root"] then bl.[Bucket, go!"tx"] ↦ B1.bv.tx'
          else bl.[Bucket, go!"tx"] ↦□ B1.bv.tx') : IProp GF) $$ [Htx]
    · rw [hbtx]
      by_cases hroot : bl = tx.[Tx, go!"root"]
      · rw [if_pos hroot]
        iexists DFrac.own 1
        iframe
        iintro H; iexact H
      · rw [if_neg hroot]
        icases Htx with #Htx
        iexists DFrac.discard
        isplitr
        · iexact Htx
        · iintro _; iexact Htx
    icases Htxf with ⟨%dqb, Htx, Htxb⟩
    unfold txFields
    icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
    try wp_auto
    wp_apply hPgid X1.t.t.meta' X1.t.mv (DFrac.own 1) $$ [Hmv] as Hmv
    · iframe
    have Hlt : rr.nv.pgid'.toNat < X1.t.mv.pgid'.toNat := by
      cases HsT.wf with | page _ _ _ hlt _ _ _ _ => exact hlt
    try wp_auto
    rw [decide_eq_false (by word)]
    try wp_auto
    wp_method_call
    try wp_call
    try wp_auto
    wp_apply hSRP B1.bv.InBucket' B1.ib rr.nv.pgid' $$ [Hibv] as Hibv
    · iframe
    try wp_auto
    ihave Hn : (rt ↦ rr.nv : IProp GF)
      $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hn := Hnback $$ Hn
    ihave Htx := Htxb $$ Htx
    have Hrt0 : rt ≠ null := by
      intro h0; rw [h0, (Hstep.2.2.2.1.2.2.1.2.2.1 bl B1 HB1).2] at Hrr; cases Hrr
    ihave Hh := Hback $$ %(bkRooted B1 rt rr.nv.pgid') %(fun _ => rr) [] [Hn] [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo] [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs] Hrf
    · ipureintro
      refine ⟨?_, fun _ _ => rfl, rfl, ?_⟩
      · intro l hl; rw [List.mem_singleton.1 hl]; exact Hrr
      · intro l hl; rw [List.mem_singleton.1 hl, Hrpar]; exact Ne.symm Hrt0
    · iapply BigSepL.bigSepL_singleton.2; rw [decide_eq_true Hrtl]; iexact Hn
    · dsimp only [bkRooted]
      iframe
    · iframe
    ihave Hw := Hclose $$ %(X1.setBkt bl (bkRooted B1 rt rr.nv.pgid')) [] Hh Hv Hst
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    try wp_auto
    iapply HΦ
    unfold bkPost
    ileft
    isplitr
    · ipureintro; rfl
    iexists X1.setBkt bl (bkRooted B1 rt rr.nv.pgid'), w1, st
    iframe
    ipureintro
    refine ⟨?_, Or.inr ⟨HrnN, X1, N ++ T, B1, rt, rr, S, D', h', Hfr, HB1, Hrr, Hrtl, Hrsp, Hrpar,
      rfl, HsT, HD', Hsi', HD1, HD2, ?_, ?_⟩⟩
    · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := Hstep
      exact ⟨s1, s2, s3, spG_bkRooted _ s4 HB1 Hrr Hrpar Hrtl Hroot, s5, s6, s7, s8⟩
    · rw [← treeEls_entries, show spP (X1.setBkt bl (bkRooted B1 rt rr.nv.pgid')) = spP X1 from rfl,
        HEls, HEd]
    · exact plainTree_of_els HsT HEls HEp
  · cases err with
    | nil => exact absurd rfl hne
    | ok ii =>
    try wp_auto
    iapply HΦ
    unfold bkPost
    iright
    isplitr
    · ipureintro; exact hne
    isplitr
    · iexact HeOk
    iexists X1, w1, st
    isplitr
    · ipureintro; exact Hst1
    iexact Hcase

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
