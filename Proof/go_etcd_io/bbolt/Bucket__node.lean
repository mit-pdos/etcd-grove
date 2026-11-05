/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__node.lean` (U7d, `notes/bbolt-proof-plan.md`): the
node cache's lookup; else a fresh node (`Write.wtxHeap_fresh`), made the root node or appended to
its parent's children, read (`node.read`) from the inline page (`common.Verify`) or the view's
page (`Tx.page`), cached, registered and counted; the heap step is `Write.wtxHeap_nodeAdd_acc`.

`Bucket.node.spec` has the premise (batch 31, U7d's finding) that a file bucket's `page` field is
nil (`bktClean`'s clause; every caller has it). Without it the code reads `b.page` for a file
bucket whose `page` is set, which `matReady` does not exclude.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__node
public import Spec.go_etcd_io.bbolt.Tx__page
public import Spec.go_etcd_io.bbolt.node__read
public import Spec.go_etcd_io.bbolt.TxStats__IncNodeCount
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Verify
public import Proof.go_etcd_io.bbolt.Write.NodeAdd
public import Proof.go_etcd_io.bbolt.Read.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit [GooseSemantics] [GooseInterp] go_gctx hos hG sem package_sem in
/-- A readable page's first key slice is not nil (its key is not empty). -/
private theorem keySliceAt_ne_nil (p : Loc) (pg : List w8) (hrd : pageReadable pg)
    (hc : 0 < pageCount pg) : keySliceAt p pg 0 ≠ slice.nil := by
  have Hks := (hrd.2 0 hc).1
  have Hk32 : (if pageFlags pg = leafPageFlag then leafKsize pg 0 else branchKsize pg 0) < 2 ^ 32 := by
    split
    · unfold leafKsize; exact BitVec.isLt _
    · unfold branchKsize; exact BitVec.isLt _
  unfold keySliceAt bslice
  intro e
  have e' := congrArg GoSlice.len e
  split at e'
  all_goals
    rename_i h
    simp only [h, ↓reduceIte] at Hks Hk32
    simp only [slice.nil] at e'
    have := congrArg BitVec.toNat e'
    simp at this
    omega

omit hos package_sem in
/-- The first inode's key slice is the first entry's key, from its source. -/
private theorem wOwns_key0 (v : View) (p : Loc) (pg : List w8) (src : Src)
    (h : 0 < pageCount pg) :
    ([∗list] it;w ∈ pageInodesAt p pg;pageWsAs pg src, wOwn (GF := GF) v true it w) ⊢
      ([∗list] it;w ∈ pageInodesAt p pg;pageWsAs pg src, wOwn v true it w) ∗
      srcOwn v (keySliceAt p pg 0) src (wKey (pageWsAs pg src) 0) := by
  have h1 : (pageInodesAt p pg)[0]? = some (pageInodeAt p pg 0) := by simp [pageInodesAt, h]
  obtain ⟨w0, h2⟩ : ∃ w0, (pageWsAs pg src)[0]? = some w0 :=
    ⟨_, List.getElem?_eq_getElem (by simp [pageWsAs, pageWs, h])⟩
  have hks : w0.ks = src := by
    simp only [pageWsAs, List.getElem?_map, Option.map_eq_some_iff] at h2
    obtain ⟨_, -, rfl⟩ := h2; rfl
  have hkey : wKey (pageWsAs pg src) 0 = w0.key := by simp [wKey, h2]
  have hk : (pageInodeAt p pg 0).key' = keySliceAt p pg 0 := by
    unfold pageInodeAt; split <;> rfl
  iintro H
  icases BigSepL2.bigSepL2_lookup_acc h1 h2 $$ H with ⟨Hw, Hback⟩
  unfold wOwn
  isimp only [↓reduceIte] at Hw
  icases Hw with ⟨%Hf, #Hk, #Hv⟩
  isplitl
  · iapply Hback
    isplitr
    · ipureintro; exact Hf
    isimp only [↓reduceIte]
    iframe #
  rw [hkey, ← hk, ← hks]
  iexact Hk

omit hos package_sem in
/-- A bucket's `tx` field, at some fraction (the root bucket's owned, a handle's persistent), and
back. -/
theorem bkt_tx_acc (bl t : Loc) (c : Prop) [Decidable c] :
    (if c then bl.[Bucket, go!"tx"] ↦ t else bl.[Bucket, go!"tx"] ↦□ t : IProp GF) ⊢
      ∃ dq, bl.[Bucket, go!"tx"] ↦{dq} t ∗ (bl.[Bucket, go!"tx"] ↦{dq} t -∗
        (if c then bl.[Bucket, go!"tx"] ↦ t else bl.[Bucket, go!"tx"] ↦□ t : IProp GF)) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]
    iintro H
    iexists DFrac.own 1
    iframe H
    iintro H; iexact H
  · simp only [h, ↓reduceIte]
    iintro #H
    iexists DFrac.discard
    isplitl []
    · iexact H
    · iintro -; iexact H

theorem Bucket.node.wp_proof (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hV : internal.common.Verify.spec (GF := GF) (hG := hG))
    (hpage : Tx.page.spec (GF := GF) (hG := hG))
    (hread : node.read.spec (GF := GF) (hG := hG))
    (hinc : TxStats.IncNodeCount.spec (GF := GF) (hG := hG)) :
    Bucket.node.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B pgid parent hB hlB hnodes hnn hready hpg0
  unfold wtxW wtxCore
  wp_start as ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hvo, Hst⟩,
    Hcells, ⟨%ml, Hmf⟩⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  have hobj := bobjs_bkt X.t bl B hB
  icases wtxHeap_bkt_obj_acc tx (DFrac.own 1) X bl B hobj $$ Hh with ⟨Hb, Hhb⟩
  rw [show decide (bl ∈ X.liveB) = true from decide_eq_true hlB]
  simp only [objOwn]
  icases Hb with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  wp_auto
  rw [show decide (B.bv.nodes' = map.nil) = false from decide_eq_false hnodes]
  wp_apply hA
  try wp_auto
  wp_apply wp_map_lookup1 $$ [H8] as H8
  · iexact H8
  have htx : B.bv.tx' = tx := Hok.2.2.1 bl B hB
  cases hnm : B.nm !! pgid with
  | some l0 =>
    -- cached
    have hl0 : l0 ≠ null := hnn l0 hnm
    simp only [Option.getD_some]
    wp_if_destruct
    · exact absurd rfl hl0
    try wp_auto
    ihave Hh := Hhb $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]
    · iframe
    iapply HΦ
    iexists X
    iframe; iframe #
    ipureintro
    exact ⟨Hr, Or.inl ⟨rfl, rfl⟩⟩
  | none =>
    obtain ⟨hmr, hpar⟩ := hready hnm
    obtain ⟨pa, pg, hwp, hrd, hfl, hein, hid, hpm, hsrc, hpa, hpm2, hend⟩ := hmr
    simp only [Option.getD_none]
    ihave Hh := Hhb $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]
    · iframe
    wp_auto
    -- the fresh node
    icases Write.wtxHeap_fresh tx X «$r0_ptr» _ $$ [Hh «$r0»] with ⟨Hh, Hn, %Hfresh⟩
    · iframe
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn0⟩
    have hnl0 : X.nloc.lookup «$r0_ptr» = none := by
      cases h : X.nloc !! «$r0_ptr» with
      | none => rfl
      | some y =>
        have := Hok.2.2.2.2.1 _ y h
        rw [Hfresh] at this; cases this
    iunfold nlAuth at Hnl
    icases Hnl with ⟨Hnl, #Hnlf⟩
    imod (ghost_map_insert_persist «$r0_ptr» (bl, pgid.toNat) hnl0) $$ Hnl with ⟨Hnl, #Hnfr⟩
    ihave #Hnlf := nlFrags_insert r X.nloc «$r0_ptr» (bl, pgid.toNat) hnl0 $$ [Hnlf Hnfr]
    · iframe #
    ihave Hnl : nlAuth (GF := GF) r 1 (X.nloc.insert «$r0_ptr» (bl, pgid.toNat)) $$ [Hnl]
    · unfold nlAuth; iframe; iframe #
    -- the parent, if any
    let Ls : List Loc := if parent = null then [] else [parent]
    have hLs : ∃ f : Loc → NRec, ∀ k ∈ Ls, B.ns !! k = some (f k) ∧ (f k).nv.isLeaf' = false ∧
        k ∈ X.live := by
      rcases hpar with hp | ⟨rp, hrp, hleaf, hlive⟩
      · refine ⟨fun _ => ⟨zero_val node, [], [], [], [], Src.stale, true⟩, ?_⟩
        intro k hk; simp [Ls, hp] at hk
      · refine ⟨fun _ => rp, ?_⟩
        intro k hk
        by_cases hp : parent = null
        · simp [Ls, hp] at hk
        · simp only [Ls, hp, ↓reduceIte, List.mem_singleton] at hk
          subst hk; exact ⟨hrp, hleaf, hlive⟩
    obtain ⟨f, hf⟩ := hLs
    have hnd : Ls.Nodup := by
      by_cases hp : parent = null <;> simp [Ls, hp]
    icases Write.wtxHeap_nodeAdd_acc tx X bl «$r0_ptr» B Ls f hB hnd (fun k hk => (hf k hk).1)
      Hfresh $$ Hh with ⟨HL, Hbo, Hf, Hrf, Hback⟩
    rw [show decide (bl ∈ X.liveB) = true from decide_eq_true hlB]
    isimp only [objOwn] at Hbo
    icases Hbo with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
    wp_join iprop(∃ (rn : Loc) (f' : Loc → NRec),
        n_ptr ↦ «$r0_ptr» ∗ b_ptr ↦ bl ∗ parent_ptr ↦ parent ∗
        bl.[Bucket, go!"rootNode"] ↦ rn ∗
        ([∗list] k ∈ Ls, objOwn X.v k (DFrac.own 1) (decide (k ∈ X.live)) (.node bl (f' k))) ∗
        ⌜(parent = null → rn = «$r0_ptr») ∧ (parent ≠ null → rn = B.bv.rootNode') ∧
          ∀ k ∈ Ls, (f' k).cs = (f k).cs ++ [«$r0_ptr»] ∧ (f' k).ws = (f k).ws ∧
            (f' k).ins = (f k).ins ∧ (f' k).key = (f k).key ∧ (f' k).ksrc = (f k).ksrc ∧
            (f' k).capOwn = (f k).capOwn ∧
            (f' k).nv = { (f k).nv with children' := (f' k).nv.children' }⌝)
      at next with [n b parent H5 HL] as ⟨%rn, %f', n, b, parent, H5, HL, %Hjoin⟩
    · by_cases hp : parent = null
      · rw [decide_eq_true hp]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iexists «$r0_ptr», f
        iframe
        ipureintro
        refine ⟨fun _ => rfl, fun h => absurd hp h, ?_⟩
        intro k hk; simp [Ls, hp] at hk
      · rw [decide_eq_false hp]
        have hLs1 : Ls = [parent] := by simp [Ls, hp]
        obtain ⟨hfp, hleafp, hlivep⟩ := hf parent (by rw [hLs1]; exact List.mem_singleton_self _)
        rw [hLs1]
        ihave HP := (BigSepL.bigSepL_singleton (Φ := fun _ k => objOwn (GF := GF) X.v k
          (DFrac.own 1) (decide (k ∈ X.live)) (.node bl (f k)))).1 $$ HL
        rw [show decide (parent ∈ X.live) = true from decide_eq_true hlivep]
        isimp only [objOwn] at HP
        icases HP with ⟨P1, P2, P3, P4, P5, P6, P7⟩
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_apply wp_slice_append $$ [$P5 $P6 $Hsl] as %s' ⟨P5, P6, -⟩
        try wp_auto
        let rp' : NRec := ⟨{ (f parent).nv with children' := s' }, (f parent).ins, (f parent).ws,
          (f parent).cs ++ [«$r0_ptr»], (f parent).key, (f parent).ksrc, (f parent).capOwn⟩
        isplitl []
        · ipureintro; rfl
        iexists B.bv.rootNode', (fun _ => rp')
        iframe n b parent H5
        isplitl [P1 P2 P3 P4 P5 P6 P7]
        · iapply (BigSepL.bigSepL_singleton (Φ := fun _ k => objOwn (GF := GF) X.v k
            (DFrac.own 1) (decide (k ∈ X.live)) (.node bl rp'))).2
          rw [show decide (parent ∈ X.live) = true from decide_eq_true hlivep]
          simp only [objOwn, rp']
          iframe
        ipureintro
        refine ⟨fun h => absurd h hp, fun _ => rfl, ?_⟩
        intro k hk
        rw [List.mem_singleton] at hk; subst hk
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    -- the page: the inline page, or the view's through `Tx.page`
    let src' : Src := if B.ib.root' = W64 0 then Write.inlSrc B else Src.view
    icases Hmf with ⟨Hmf, %Hml⟩
    icases bkt_tx_acc bl B.bv.tx' (bl = B.bv.tx'.[Tx, go!"root"]) $$ H2 with ⟨%dqt, H2, H2b⟩
    wp_join iprop(p_ptr ↦ pa ∗ b_ptr ↦ bl ∗ pgId_ptr ↦ pgid ∗
        bl.[Bucket, go!"tx"] ↦{dqt} B.bv.tx' ∗ txFields tx (DFrac.own 1) X ∗
        tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗
        mapFields r.db (DFrac.own (1 : Qp).half.half) (some (X.v.base, ml)) ∗ viewCells wq X.v ∗
        (if True then pageOwn X.v B else emp) ∗ srcLoc X.v pa src' pg)
      at next with [p b pgId H2 Hf Hdb Hmf Hcells H10]
      as ⟨p, b, pgId, H2, Hf, Hdb, Hmf, Hcells, H10, Hsrc⟩
    · by_cases hin0 : B.ib.root' = W64 0
      · -- inline: position 0, the bucket's page
        have hw := hwp
        unfold wpageAt at hw
        rw [if_pos hin0] at hw
        split at hw
        · rename_i hp0
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨hpaq, hpgq⟩ := hw
          subst hp0
          have hpn0 : B.bv.page' ≠ null := by
            intro e; rw [← hpaq, e] at hpa; simp [null] at hpa
          rw [decide_eq_false hpn0]
          wp_auto
          wp_apply (hV _ iprop(pgId_ptr ↦ W64 0)) $$ [pgId]
          · isplit
            · wp_auto
              iframe
            · iframe
          iintro pgId
          try wp_auto
          isimp only [↓reduceIte] at H10
          icases Write.pageOwn_srcLoc X.v B (hsrc hin0) hpn0 $$ H10 with ⟨H10, Hs⟩
          isplitl []
          · ipureintro; rfl
          rw [← hpaq, ← hpgq]
          simp only [src', if_pos hin0, ↓reduceIte]
          iframe
        · cases hw
      · -- a file bucket: its page field is nil
        have hpn : B.bv.page' = null := hpg0 hnm hin0
        rw [decide_eq_true hpn]
        have hw := hwp
        unfold wpageAt at hw
        rw [if_neg hin0] at hw
        obtain ⟨pg', hpg', hpe⟩ := Option.map_eq_some_iff.mp hw
        simp only [Prod.mk.injEq] at hpe
        obtain ⟨hpaq, rfl⟩ := hpe
        ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
        isimp only [mapFields] at Hmf
        icases Hmf with ⟨Hdref, Hdata, Hm0, Hm1, %Hlen⟩
        have hbound := Hml pgid.toNat pg' hpg'
        icases viewCells_page_acc _ X.v pgid.toNat pg' hpg' $$ Hcells with ⟨Hpg, Hcells⟩
        rw [show pageLoc X.v pgid.toNat = pa from hpaq]
        isimp only [txFields] at Hf
        icases Hf with ⟨Hw, Hm, Hmeta, Hpgs, Hch, Hwf, Hmv, Hpm, Hbufs⟩
        ihave %Hpmnn := ownMap_not_nil _ _ _ $$ Hpm
        have Hsp := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"pages"]) X.t.t.pages'
          (QpMul 1 (1 : Qp).half) (QpMul 1 (1 : Qp).half)
        rw [qpMul_half_add] at Hsp
        icases Hsp.1 $$ Hpgs with ⟨Hp1, Hp2⟩
        have Hsd := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"db"]) r.db
          (QpMul 1 (1 : Qp).half) (QpMul 1 (1 : Qp).half.half)
        rw [← txDbQ_eq] at Hsd
        icases Hsd.1 $$ Hdb with ⟨Hd1, Hd2⟩
        ihave #Hps := BC.core_pageSize K $$ Hcore
        rw [Hr.1] at Hsd ⊢
        have h16 : 16 ≤ pg'.length := by have := hrd.1; unfold elemOff at this; omega
        wp_auto
        rw [htx]
        wp_apply (hpage tx K.db X.t.t.pages' X.t.pm X.v.base pgid pa pg'
          (DFrac.own (QpMul 1 (1 : Qp).half)) (DFrac.own 1) (DFrac.own (Qp.half 1).half)
          (DFrac.own wq) (Or.inr ⟨hpm, Hnn, by omega, hpaq.symm⟩) h16 (by unfold pageId; rw [hid])
          (by rcases hfl with h | h <;> simp [h]))
          $$ [Hp1 Hpm Hd1 Hdata Hpg] as ⟨Hp1, Hpm, Hd1, Hdata, Hpg⟩
        · iframe; iframe #; rw [if_neg (show ¬ X.t.t.pages' = null from Hpmnn)]; iframe
        rw [if_neg (show ¬ X.t.t.pages' = null from Hpmnn)]
        try wp_auto
        ihave Hcells := Hcells $$ Hpg
        ihave Hpgs := Hsp.2 $$ [Hp1 Hp2]
        · iframe
        ihave Hdb := Hsd.2 $$ [Hd1 Hd2]
        · iframe
        isplitl []
        · ipureintro; rfl
        rw [← htx]
        simp only [src', if_neg hin0, ↓reduceIte, srcLoc, txFields, mapFields]
        iframe
        ipureintro
        refine ⟨Hlen, ⟨pgid.toNat, pg', 0, hpg', by simp, by simp [bytesAt], ?_⟩⟩
        rw [← hpaq]; simp [pageLoc]
    -- read the page into the node
    have hsrc' : src' ≠ Src.stale := by
      simp only [src', Write.inlSrc]; split <;> (try split) <;> simp
    wp_apply (hread X.v «$r0_ptr» _ pa src' pg wq hrd hfl hpa hpm2 hend hein) $$ [Hn Hsrc Hcells]
      as ⟨%s, Hn, Hs, Hcap, Hws, Hsrc, Hcells⟩
    · iframe
    try wp_auto
    -- cache it, count it
    wp_apply (wp_mapInsert Pgid.ty B.bv.nodes' B.nm pgid «$r0_ptr») $$ [H8] as H8
    · iexact H8
    try wp_auto
    rw [htx]
    wp_apply hinc K tx r m 1 (W64 1) $$ [Hst] as %st' Hst
    · iframe; iframe #
    try wp_auto
    -- the new records
    let key : GoSlice := if 0 < pageCount pg then keySliceAt pa pg 0 else slice.nil
    let nv0 : node := ⟨bl, false, false, false, slice.nil, W64 0, parent, slice.nil, slice.nil⟩
    let r0 : NRec := ⟨nodeAfterRead nv0 pg s key, pageInodesAt pa pg, pageWsAs pg src', [],
      wKey (pageWsAs pg src') 0, src', true⟩
    have hkey : 0 < pageCount pg → keySliceAt pa pg 0 ≠ slice.nil :=
      fun hc => keySliceAt_ne_nil pa pg hrd hc
    ihave Ho : objOwn X.v «$r0_ptr» (DFrac.own 1) true (.node bl r0) $$ [Hn Hs Hcap Hws]
    · ihave Hc0 := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
      ihave Hc1 := ownSliceCap_nil (V := Loc) (GF := GF)
      by_cases hc : 0 < pageCount pg
      · icases wOwns_key0 X.v pa pg src' hc $$ Hws with ⟨Hws, #Hk⟩
        simp only [objOwn, r0, nodeAfterRead, key, nv0, if_pos hc, ↓reduceIte,
          _root_.true_and, ne_eq, hkey hc, not_false_eq_true]
        iframe; iframe #
      · simp only [objOwn, r0, nodeAfterRead, key, nv0, if_neg hc, ↓reduceIte, _root_.true_and,
          ne_eq, not_true_eq_false]
        iframe; iframe #
    let B' : BRec := ⟨{ B.bv with rootNode' := rn }, B.ib, B.nm.insert pgid «$r0_ptr», B.bm, (if parent = null then B.ns else B.ns.insert parent (f' parent)), B.ipg, B.isrc, B.pst⟩
    ihave H2 := H2b $$ H2
    ihave Hbo : objOwn X.v bl (DFrac.own 1) true (.bkt B') $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]
    · simp only [objOwn, B']
      rw [htx]
      iframe
    have hLsB : ∀ k ∈ Ls, B'.ns !! k = some (f' k) := by
      intro k hk
      by_cases hp : parent = null
      · simp [Ls, hp] at hk
      · simp only [Ls, hp, ↓reduceIte, List.mem_singleton] at hk
        subst hk
        simp [B', hp]
    have hLsO : ∀ k, k ∉ Ls → B'.ns !! k = B.ns !! k := by
      intro k hk
      by_cases hp : parent = null
      · simp [B', hp]
      · have hkp : parent ≠ k := by
          intro e; subst e; exact hk (by simp [Ls, hp])
        simp only [B', hp, ↓reduceIte]
        exact GMap.lookup_insert_ne _ _ hkp
    have hparL : ∀ k ∈ Ls, (f' k).nv.parent' ≠ k := by
      intro k hk
      rw [(Hjoin.2.2 k hk).2.2.2.2.2.2]
      exact Hok.2.2.2.1 bl B k (f k) hB (hf k hk).1
    have hparN : r0.nv.parent' ≠ «$r0_ptr» := by
      show parent ≠ «$r0_ptr»
      by_cases hp : parent = null
      · rw [hp]; exact Ne.symm Hnn0
      · intro e
        have hk : parent ∈ Ls := by simp [Ls, hp]
        have := Write.objs_isSome_node X.t bl B parent hB (by rw [(hf parent hk).1]; rfl)
        rw [e, Hfresh] at this; cases this
    ihave Hh := Hback $$ %B' %f' %r0 [] [HL] [Hbo] [Hf] [Hrf] [Ho]
    · ipureintro; exact ⟨hLsB, hLsO, htx, hparL, hparN⟩
    · iexact HL
    · iexact Hbo
    · iexact Hf
    · iexact Hrf
    · iexact Ho
    let Y : WX := (X.setBkt bl B').addNode bl «$r0_ptr» B' r0
    have hYl : (Y.t.objs !! «$r0_ptr»).isSome :=
      Write.objs_isSome_node Y.t bl { B' with ns := B'.ns.insert «$r0_ptr» r0 } «$r0_ptr»
        (by simp [Y, WX.addNode, WX.setBkt]) (by simp)
    ihave Hh := Write.wtxHeap_nloc_insert tx (DFrac.own 1) Y «$r0_ptr» (bl, pgid.toNat) hYl $$ Hh
    iapply HΦ
    iexists { Y with nloc := X.nloc.insert «$r0_ptr» (bl, pgid.toNat) }
    iframe; iframe #
    isplitl [Hmf]
    · isplitr
      · ipureintro; exact Hr
      iexists ml
      iframe
      ipureintro; exact Hml
    ipureintro
    refine Or.inr ?_
    obtain ⟨hJ1, hJ2, hJ3⟩ := Hjoin
    refine ⟨B, pa, pg, r0, B'.ns.insert «$r0_ptr» r0, { B.bv with rootNode' := rn }, hB, hwp, hnm,
      Hnn0, by simp [Hfresh], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, hsrc', ?_, ?_, ?_,
      ?_, ?_⟩
    · show (pageWsAs pg src').map wDat = (pageWsAs pg (posSrc B)).map wDat
      unfold pageWsAs; simp only [List.map_map]; rfl
    · intro w hw
      simp only [r0, pageWsAs, List.mem_map] at hw
      obtain ⟨w', -, rfl⟩ := hw
      refine ⟨hsrc', ?_⟩
      dsimp only
      split
      · exact hsrc'
      · simp
    · simp [r0, pageInodesAt, pageWsAs, pageWs]
    · show (if 0 < pageCount pg then keySliceAt pa pg 0 else slice.nil) = slice.nil ↔
        pageWsAs pg src' = []
      by_cases hc : 0 < pageCount pg
      · rw [if_pos hc]
        simp only [pageWsAs, pageWs, List.map_eq_nil_iff, List.range_eq_nil]
        constructor
        · intro h; exact absurd h (hkey hc)
        · intro h; omega
      · rw [if_neg hc]
        simp only [pageWsAs, pageWs, List.map_eq_nil_iff, List.range_eq_nil]
        constructor
        · intro _; omega
        · intro _; trivial
    · intro w hw _
      simp only [r0, pageWsAs, List.mem_map] at hw
      obtain ⟨w', -, rfl⟩ := hw
      dsimp only
      have hs2 : src' = Src.view ∨ src' = Src.own DFrac.discard := by
        simp only [src', Write.inlSrc]
        split
        · split <;> simp
        · simp
      split
      · exact hs2
      · right; rfl
    · by_cases hp : parent = null
      · left
        refine ⟨hp, by rw [hJ1 hp], ?_⟩
        simp [B', hp]
      · right
        have hk : parent ∈ Ls := by simp [Ls, hp]
        obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hJ3 parent hk
        refine ⟨hp, by rw [hJ2 hp], f parent, f' parent, (hf parent hk).1, (hf parent hk).2.1,
          hc1, hc2, hc3, hc4, hc5, hc6, hc7, ?_⟩
        simp [B', hp]
    · simp only [Y, WX.addNode, WX.setBkt, GMap.insert_insert]
      rfl

end proof

end bbolt
end EtcdGrove
end Perennial
