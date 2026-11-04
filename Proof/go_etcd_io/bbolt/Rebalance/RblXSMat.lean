/-
`rblX` through a materialization during rebalance (U8b, `Rebalance/RblXSteps.lean`'s
`rblX_mat`): a branch node's unmaterialized child page made a node (`nodeAdded`). The bucket's
`rblB` is `RblMat`'s `rbl_nodeAdded`; the logical tree changes by data only (U7's
`Write.ltree_nodeAdded'`), so the trees, positions, extents and covers are kept; the new node is
fresh, live, registered and reached through its parent. `l` unregistered (`hnl`) is `heapOK`'s
(a registered node is an object; `nodeAdded`'s `l` is none).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSMatT
public import Proof.go_etcd_io.bbolt.Rebalance.RblMat
public import Proof.go_etcd_io.bbolt.Write.MatOK

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section mat
variable [GooseExts]

/-- **A sibling, or a branch's child, materialized** (`b.node` of the parent's entry `i`, a page
position): the invariant kept; the unbalanced nodes after are the ones before. -/
theorem rblX_mat (X X' : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (l : Loc) (pgid : w64)
    (parent : Loc) (i : Nat) (hI : rblX X fl bl dfc) (h : nodeAdded X X' bl l pgid parent)
    (hpos : ∃ B, X.t.bs !! bl = some B ∧ pagePosAt B parent i pgid)
    (hnl : X.nloc !! l = none) :
    rblX X' fl bl dfc ∧ rblRel X fl X' fl X.t.mv.txid' ∧
      ∀ B B', X.t.bs !! bl = some B → X'.t.bs !! bl = some B' → ∀ y ry', B'.ns !! y = some ry' →
        ry'.nv.unbalanced' = true →
        ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid' := by
  obtain ⟨B, hb, hpp⟩ := hpos
  obtain ⟨⟨htw, hpm, hhwm, htx, hrlS⟩, hBk, hEB, hH, hL, hN, hV, hLR, hFV, hU, hX, hPL, hOD, hRH⟩ :=
    hI
  obtain ⟨hrb, hbmt, hnest0, -, hlive⟩ := hBk bl B hb
  rw [if_pos rfl] at hrb
  have hrb' := hrb
  obtain ⟨hc, ⟨bnd, hk⟩, ha, hht⟩ := hrb'
  have hpp' := hpp
  obtain ⟨rp, w, hrp, hbr, hw, hwp, hnone⟩ := hpp'
  subst hwp
  have h0 : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 parent rp hrp; rw [hbr] at this; cases this
  have hlo : (X.t.objs !! l).isNone := by obtain ⟨_, _, _, _, _, _, _, _, _, _, h5, _⟩ := h; exact h5
  have hfresh : B.ns !! l = none := by
    cases hl' : B.ns !! l with
    | none => rfl
    | some _ =>
      have := (objs_isSome X.t l).2 (Or.inr ⟨bl, B, hb, by rw [hl']; rfl⟩)
      rw [Option.isNone_iff_eq_none] at hlo; rw [hlo] at this; cases this
  have hlns : ∀ c C, X.t.bs !! c = some C → C.ns !! l = none := by
    intro c C hC
    cases hl' : C.ns !! l with
    | none => rfl
    | some _ =>
      have := (objs_isSome X.t l).2 (Or.inr ⟨c, C, hC, by rw [hl']; rfl⟩)
      rw [Option.isNone_iff_eq_none] at hlo; rw [hlo] at this; cases this
  have hdead : X.t.dead !! l = none := by
    cases hl' : X.t.dead !! l with
    | none => rfl
    | some _ =>
      have := (objs_isSome X.t l).2 (Or.inl (by rw [hl']; rfl))
      rw [Option.isNone_iff_eq_none] at hlo; rw [hlo] at this; cases this
  have hmf : matFresh X bl l := by
    intro B1 hB1
    rw [hb] at hB1; cases hB1
    refine ⟨fun c hc' => ?_, fun h0' => absurd h0' h0⟩
    obtain ⟨-, r0, hr0, -⟩ := hc.2.2.2.2.1 c l hc'
    rw [hfresh] at hr0; cases hr0
  have hleaf : ∀ B1 pa pg, X.t.bs !! bl = some B1 → B1.ib.root' = W64 0 →
      B1.bv.rootNode' = null → wpageAt X.v B1 w.pgid = some (pa, pg) →
      pageFlags pg = leafPageFlag := by
    intro B1 pa pg hB1 h0'; rw [hb] at hB1; cases hB1; exact absurd h0' h0
  obtain ⟨hroot, hbkt, hleaves, hvv, hfuel, hrpid, hrl', hbs⟩ :=
    Write.nodeAdded_facts X X' bl l w.pgid parent h hmf hleaf
  have hlt := Write.ltree_nodeAdded' X X' bl l w.pgid parent h hmf
  have hlt' : ∀ c q, Write.ldat (ltree X' c q) = Write.ldat (ltree X c q) := fun c q =>
    hlt c q (fun hcb B1 hB1 h0' => by subst hcb; rw [hb] at hB1; cases hB1; exact absurd h0' h0)
  have hpos' : ∀ c, X'.positions c = X.positions c := by
    intro c; unfold WX.positions; rw [hfuel, hrpid]
    exact Write.lposF_congr _ _ c (fun q => Write.shp_of_ldat _ _ (hlt' c q)) _ _
  -- the records
  have h' := h
  obtain ⟨B0, pa, pg, r, ns', bv', hB0, hwpg, -, hl0, -, hrbk, hrpar, hrid, hrleaf, hru, hrs, hrcs,
    hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := h'
  rw [hb] at hB0; cases hB0
  have hpnl : parent ≠ null := (hc.2.2.2.2.1 _ _ (ncol_nm (hc.2.2.2.2.2.2.2.1 parent rp hrp))).1
  have hpg : X.v.pages !! w.pgid.toNat = some pg := by
    unfold wpageAt at hwpg; rw [if_neg h0] at hwpg
    cases h2 : X.v.pages !! w.pgid.toNat with
    | none => rw [h2] at hwpg; cases hwpg
    | some pg0 => rw [h2] at hwpg; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwpg
                  rw [hwpg.2]
  rcases hcase with ⟨hpn, -, -⟩ | ⟨-, hbv, rp0, rp', hrp0, -, hc1, hc2, hc3, hc4, hc5, hcp, hc6, hns⟩
  · exact absurd hpn hpnl
  rw [hrp] at hrp0; cases hrp0
  subst hbv; subst hns
  have hbsX : ∀ c, X'.t.bs !! c = if c = bl then some (matBkt B w.pgid parent l rp' r)
      else X.t.bs !! c := by
    intro c; rw [hX']
    show (X.t.bs.insert bl _) !! c = _
    by_cases hcb : c = bl
    · subst hcb; rw [GMap.lookup_insert, if_pos rfl]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hcb), if_neg hcb]
  have hB' : X'.t.bs !! bl = some (matBkt B w.pgid parent l rp' r) := by rw [hbsX, if_pos rfl]
  have hrl : (matBkt B w.pgid parent l rp' r).ns !! l = some r := by rw [mat_ns, if_pos rfl]
  have hrp' : (matBkt B w.pgid parent l rp' r).ns !! parent = some rp' := by
    rw [mat_ns, if_neg (fun h => by rw [h, hfresh] at hrp; cases hrp), if_pos rfl]
  have hr : matNew bl parent pg r :=
    ⟨hrbk, hrpar, hrid, hrleaf, hru, hrs, hrcs, hrco, by rw [hrws, mat_pageWsAs_wDat], hrlive,
      hrkey, hrks⟩
  have hp' : matParent rp rp' l := ⟨hc1, hc2, hc3, hc4, hc5, hc6, hcp⟩
  have hstrict := mat_strict X.v hV
  have hl : l ≠ null := hl0
  obtain ⟨-, -, -, hlnl, hpgc, hid, -, -, -⟩ :=
    mat_basic X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hnsB := mat_nsB X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg hpg
    r rp' hr hp'
  have hold := mat_old X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg hpg
    r rp' hr hp'
  obtain ⟨B1, hB1, hv1, hrbB1, hent1, -, -, -, -, -, hunb1, -⟩ :=
    rbl_nodeAdded X X' _ bl l w.pgid parent B dfc i hb hV hrb h hpp hfresh
  rw [hB'] at hB1; cases hB1
  let B' := matBkt B w.pgid parent l rp' r
  have hrid' : r.nv.pgid' = w.pgid := by rw [hrid, hid]
  -- the extents
  have hext : ∀ c q, X'.posExtent c q = X.posExtent c q := by
    intro c q
    apply Write.posExtent_eq X X' c q hvv
    rw [hbsX]
    split
    · rename_i hcb; subst hcb; rw [hb]
      simp only [Option.map_some, Option.some.injEq]
      unfold Write.posIdOf resolve
      have h0' : B'.ib.root' ≠ W64 0 := h0
      rw [if_neg h0', if_neg h0]
      show (match (B.nm.insert w.pgid l) !! q with
        | some l => ((B'.ns !! l).map fun (r : NRec) => r.nv.pgid').getD 0 | none => q) = _
      by_cases hq : q = w.pgid
      · subst hq; rw [GMap.lookup_insert, hnone]
        simp only
        rw [hrl]; exact hrid'
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hq)]
        cases hq' : B.nm !! q with
        | none => rfl
        | some l' =>
          simp only
          obtain ⟨-, r0, hr0, -⟩ := hc.2.2.2.2.1 q l' hq'
          obtain ⟨r0', h1, -, -, -, h5, -⟩ := hnsB l' r0 hr0
          rw [h1, hr0]; simp only [Option.map_some, Option.getD_some, h5]
    · rfl
  have hcovW : coverW X' = coverW X := by
    funext s c
    cases c with
    | pos c q =>
      unfold coverW
      have hd : (X'.t.bs !! c ≠ none) ↔ (X.t.bs !! c ≠ none) := by
        rw [Ne, Ne, ← Option.not_isSome_iff_eq_none, ← Option.not_isSome_iff_eq_none, hbs]
      simp only [hd, hpos', hext]
    | bkt nm =>
      unfold coverW
      rw [hroot, hvv]
      simp only [hbkt]
  have hlc : ∀ s, lCovers X' s ↔ lCovers X s := by
    intro s; rw [lCovers_iff, lCovers_iff, hcovW]
  have hblX : X.t.bs !! bl ≠ none := by rw [hb]; simp
  -- the finite trees
  have hrtx : ∀ c, rtOK X c → rtOK X' c := by
    intro c ⟨t, ht, hp, hh, D, hD⟩
    obtain ⟨t', ht', hpid, hht, hdps⟩ := ltIs_ldat (ltree X) (ltree X') c (hlt' c) t ht
    exact ⟨t', ht', by rw [hpid, hp, hrpid], by rw [hht, hfuel]; exact hh, D,
      fun x hx => hD x (by rw [← hdps 0]; exact hx)⟩
  -- the reached nodes
  have hrootT : ∀ rt, nodeRootIn B B.bv.rootNode' rt →
      nodeRootIn (matBkt B w.pgid parent l rp' r) (matBkt B w.pgid parent l rp' r).bv.rootNode' rt := by
    intro rt hrt
    cases hrt with
    | top _ rr hrr hp0 =>
      obtain ⟨rr', h1, h2, -⟩ := hnsB _ rr hrr
      exact nodeRootIn.top _ rr' h1 (by rw [h2]; exact hp0)
    | up _ _ rr hrr hp0 _ => exact absurd (hk.2.1 rr hrr) hp0
  have hdescT : ∀ a d, descIn B a d → descIn (matBkt B w.pgid parent l rp' r) a d :=
    descIn_grow B _ (fun x rx hx => by
      obtain ⟨rx', h1, -, -, -, -, h6, -⟩ := hnsB x rx hx
      exact ⟨rx', h1, h6⟩)
  have hliveX : ∀ y, y ∈ X'.live ↔ y = l ∨ y ∈ X.live := by
    intro y; rw [hX']
    show ((X.live.insert l ()) !! y).isSome = true ↔ _
    rw [GMap.lookup_insert_eq_iff]
    by_cases hy : l = y
    · subst hy; simp
    · rw [if_neg hy]; exact ⟨fun h => Or.inr h, fun h => h.elim (fun e => absurd e.symm hy) id⟩
  have hB'cases : ∀ y ry', (matBkt B w.pgid parent l rp' r).ns !! y = some ry' →
      (y = l ∧ ry' = r) ∨ (y ≠ l ∧ ∃ ry0, B.ns !! y = some ry0 ∧ ry'.nv.isLeaf' = ry0.nv.isLeaf' ∧
        ry'.ws = ry0.ws ∧ ry'.nv.pgid' = ry0.nv.pgid') := by
    intro y ry' hy
    by_cases hyl : y = l
    · subst hyl; rw [hrl] at hy; cases hy; exact Or.inl ⟨rfl, rfl⟩
    · obtain ⟨ry0, h1, -, h3, h4, h5, -⟩ := hold y ry' hy hyl
      exact Or.inr ⟨hyl, ry0, h1, h3, h4, h5⟩
  have hobj : ∀ k, (X.t.objs !! k).isSome = true → (X'.t.objs !! k).isSome = true := by
    apply objs_isSome_mono X.t X'.t (fun k hk => by rw [hX']; exact hk)
    intro c C k hC hk; right
    by_cases hcb : c = bl
    · subst hcb; rw [hb] at hC; cases hC
      obtain ⟨ry, hry⟩ := Option.isSome_iff_exists.1 hk
      obtain ⟨ry', h1, -⟩ := hnsB k ry hry
      exact ⟨c, _, hB', by rw [h1]; rfl⟩
    · exact ⟨c, C, by rw [hbsX, if_neg hcb]; exact hC, hk⟩
  have hdead' : X'.t.dead = X.t.dead := by rw [hX']
  have hmv : X'.t.mv = X.t.mv := by rw [hX']
  have hhd : X'.handles = X.handles := by rw [hX']
  have hliveB : X'.liveB = X.liveB := by rw [hX']
  have hobjB : ∀ k, (X.t.bobjs !! k).isSome = true → (X'.t.bobjs !! k).isSome = true :=
    bobjs_isSome_mono X.t X'.t (fun k hk => by rw [hX']; exact hk) (fun c h => by rw [hbs]; exact h)
  refine ⟨⟨⟨by rw [hX']; exact htw, by rw [hX']; exact hpm, by rw [hX']; exact hhwm,
      by rw [hX']; exact htx, by rw [hrl', hbs]; exact hrlS⟩, ?_, ?_, ?_, ?_, ?_,
      by rw [hvv]; exact hV, ?_, Write.flView_congr X X' fl hvv hlc hFV,
      by unfold covU; rw [hcovW]; exact hU, by rw [hvv]; exact hX, hPL, ?_,
      fun c hc' => by rw [hrl']; rw [hX']; exact hRH c (by rw [← hbs]; exact hc')⟩, ?_, ?_⟩
  · -- buckets
    intro c C hC
    rw [hbsX] at hC
    split at hC
    · rename_i hcb; subst hcb; cases hC
      refine ⟨by rw [if_pos rfl, hmv]; exact hrbB1, fun nm d hd => by
          rw [hbs]; exact hbmt nm d hd, ?_, hrtx c (hBk c B hb).2.2.2.1, fun y ry hy => ?_⟩
      · intro k d hk'
        obtain ⟨D0, v, hD0, hev, hlen, hinl, hroot0, hib0⟩ := hnest0 k d hk'
        refine ⟨if d = c then matBkt B w.pgid parent l rp' r else D0, v, by
            rw [hbsX]; split
            · rfl
            · exact hD0, hent1 k v hev, hlen, hinl, ?_, ?_⟩
        · split
          · rename_i hd; subst hd; rw [hb] at hD0; cases hD0; exact hroot0
          · exact hroot0
        · split
          · rename_i hd; subst hd; rw [hb] at hD0; cases hD0; exact hib0
          · exact hib0
      · rcases hB'cases y ry hy with ⟨rfl, -⟩ | ⟨-, ry0, h1, -⟩
        · exact (hliveX _).2 (Or.inl rfl)
        · exact (hliveX _).2 (Or.inr (hlive y ry0 h1))
    · rename_i hcb
      obtain ⟨h1, h2, h3, h4, h5⟩ := hBk c C hC
      refine ⟨by rw [hvv, hmv]; exact h1, fun nm d hd => by rw [hbs]; exact h2 nm d hd, ?_, hrtx c h4,
        fun y ry hy => (hliveX _).2 (Or.inr (h5 y ry hy))⟩
      intro k d hk'
      obtain ⟨D0, v, hD0, hev, hlen, hinl, hroot0, hib0⟩ := h3 k d hk'
      refine ⟨if d = bl then matBkt B w.pgid parent l rp' r else D0, v, by
          rw [hbsX]; split
          · rfl
          · exact hD0, by rw [hvv]; exact hev, hlen, hinl, ?_, ?_⟩
      · split
        · rename_i hd; subst hd; rw [hb] at hD0; cases hD0; exact hroot0
        · exact hroot0
      · split
        · rename_i hd; subst hd; rw [hb] at hD0; cases hD0; exact hib0
        · exact hib0
  · -- entries bounded
    intro c C hC y ry hy x hxw
    rw [hbsX] at hC
    split at hC
    · rename_i hcb; subst hcb; cases hC
      rcases hB'cases y ry hy with ⟨hyl, hre⟩ | ⟨-, ry0, h1, h2, h3, -⟩
      · subst ry; subst y
        refine ⟨(hrbB1.1.2.2.2.2.2.2.2.1 l r hrl).2.2.2.2.1 x hxw, fun hlf hnb => ?_⟩
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hxw
        have hd : r.ws.map wDat = (pageWs pg).map wDat := by rw [hrws, mat_pageWsAs_wDat]
        obtain ⟨hjl, hjd⟩ := mat_at hd j x hj
        have hfl : pageFlags pg = leafPageFlag := by
          rw [hrleaf] at hlf; simpa using hlf
        obtain ⟨e1, -, e3, e4⟩ := mat_wDat_eq hjd
        obtain ⟨f1, -, f3, f4⟩ := mat_pageW_leaf pg j hfl
        rw [e1, f1] at hnb
        have h2 : leafFlags pg j % 2 = 0 := by
          have : ¬ (leafFlags pg j % 2 = bucketLeafFlag) :=
            fun h => hnb ((mat_isBktFlag_iff _ (mat_leafFlags_lt pg j)).2 h)
          unfold bucketLeafFlag at this; omega
        have hbd := Write.viewWF_leafBnd X.v hV _ pg hpg hfl j hjl h2
        rw [e3, f3, e4, f4]
        unfold leafKey leafValue bytesAt
        have := List.length_take_le (leafKsize pg j) (pg.drop (elemOff j + leafPos pg j))
        have := List.length_take_le (leafVsize pg j)
          (pg.drop (elemOff j + leafPos pg j + leafKsize pg j))
        omega
      · rw [h3] at hxw; rw [h2]
        exact hEB c B hb y ry0 h1 x hxw
    · exact hEB c C hC y ry hy x hxw
  · intro b nm h; rw [hhd] at h; exact hobjB b (hH b nm h)
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hL
    refine ⟨by rw [hrl', hliveB]; exact l1, fun y hy => ?_, fun c C hC => ?_,
      fun c C y ry hC hy => ?_, fun y hy hyl => ?_⟩
    · rcases (hliveX y).1 hy with rfl | hy
      · exact (objs_isSome X'.t y).2 (Or.inr ⟨bl, _, hB', by rw [hrl]; rfl⟩)
      · exact hobj y (l2 y hy)
    · rw [hbsX] at hC; split at hC
      · rename_i hcb; subst hcb; rw [hliveB]; exact l3 c B hb
      · rw [hliveB]; exact l3 c C hC
    · rw [hbsX] at hC; split at hC
      · rename_i hcb; subst hcb; cases hC
        rcases hB'cases y ry hy with ⟨rfl, -⟩ | ⟨-, ry0, h1, -⟩
        · exact (hliveX _).2 (Or.inl rfl)
        · exact (hliveX _).2 (Or.inr (l4 c B y ry0 hb h1))
      · exact (hliveX _).2 (Or.inr (l4 c C y ry hC hy))
    · rw [hdead'] at hy
      rcases (hliveX y).1 hyl with rfl | hyl
      · rw [hdead] at hy; cases hy
      · exact l5 y hy hyl
  · -- the registry
    intro y c p hy hyl
    have hnl' : X'.nloc = X.nloc.insert l (bl, w.pgid.toNat) := by rw [hX']
    rw [hnl', GMap.lookup_insert_eq_iff] at hy
    split at hy
    · rename_i hly; subst hly; cases hy
      exact ⟨_, r, hB', hrl, by rw [hrid']⟩
    · rename_i hly
      have hyl' : y ∈ X.live := ((hliveX y).1 hyl).resolve_left (fun e => hly e.symm)
      obtain ⟨C0, r0, hC0, hr0, hp⟩ := hN y c p hy hyl'
      by_cases hcb : c = bl
      · subst hcb; rw [hb] at hC0; cases hC0
        obtain ⟨r0', h1, -, -, -, h5, -⟩ := hnsB y r0 hr0
        exact ⟨_, r0', hB', h1, by rw [h5]; exact hp⟩
      · exact ⟨C0, r0, by rw [hbsX, if_neg hcb]; exact hC0, hr0, hp⟩
  · -- reached
    obtain ⟨r1, r2⟩ := hLR
    refine ⟨fun c C hC hl' => ?_, fun c C y ry hC hy hyl => ?_⟩
    · have hC0 : ∃ C0, X.t.bs !! c = some C0 := by
        rw [hbsX] at hC; split at hC
        · rename_i hcb; subst hcb; exact ⟨B, hb⟩
        · exact ⟨C, hC⟩
      obtain ⟨C0, hC0⟩ := hC0
      have hcx : c ∈ X.liveB := by rw [← hliveB]; exact hl'
      refine bktReach_mono X X' hrl' (fun d D hD => ?_) c (r1 c C0 hC0 hcx)
      by_cases hdb : d = bl
      · subst hdb; rw [hb] at hD; cases hD; exact ⟨_, hB', rfl⟩
      · exact ⟨D, by rw [hbsX, if_neg hdb]; exact hD, rfl⟩
    · rw [hbsX] at hC; split at hC
      · rename_i hcb; subst hcb; cases hC
        rcases hB'cases y ry hy with ⟨rfl, -⟩ | ⟨hyl', ry0, h1, -⟩
        · obtain ⟨rt, hrt, hd⟩ := r2 c B parent rp hb hrp (hlive parent rp hrp)
          exact ⟨rt, hrootT rt hrt, descIn_snoc _ rt parent (hdescT rt parent hd) rp' y hrp'
            (by rw [hc1]; exact List.mem_append_right _ (List.mem_singleton_self _))⟩
        · have hyx : y ∈ X.live := ((hliveX y).1 hyl).resolve_left hyl'
          obtain ⟨rt, hrt, hd⟩ := r2 c B y ry0 hb h1 hyx
          exact ⟨rt, hrootT rt hrt, hdescT rt y hd⟩
      · rename_i hcb
        have hyl' : y ≠ l := fun he => by rw [he, hlns c C hC] at hy; cases hy
        exact r2 c C y ry hC hy (((hliveX y).1 hyl).resolve_left hyl')
  · -- disjoint
    intro c C' hC' k hk c' C2 hC2 hne
    rw [hbsX] at hC'
    split at hC'
    · rename_i hcb; subst hcb; cases hC'
      rw [hbsX, if_neg hne] at hC2
      by_cases hkl : k = l
      · subst hkl
        exact hlns c' C2 hC2
      · obtain ⟨ry', hry'⟩ := Option.isSome_iff_exists.1 hk
        obtain ⟨ry0, h1, -⟩ := hold k ry' hry' hkl
        exact hOD c B hb k (by rw [h1]; rfl) c' C2 hC2 hne
    · rename_i hcb
      have o2 := hOD c C' hC' k hk
      have hkl : k ≠ l := fun he => by rw [he, hlns c C' hC'] at hk; cases hk
      rw [hbsX] at hC2; split at hC2
      · rename_i hcb'; subst hcb'; cases hC2
        have hBk' := o2 c' B hb hne
        have hkp : k ≠ parent := fun he => by rw [he, hrp] at hBk'; cases hBk'
        rw [mat_ns, if_neg hkl, if_neg hkp]; exact hBk'
      · exact o2 c' C2 hC2 hne
  · -- the relation
    have hnl' : X'.nloc = X.nloc.insert l (bl, w.pgid.toNat) := by rw [hX']
    refine ⟨hvv, by rw [hX'], hrl', fun x y hxy => ?_, by rw [hX'], by rw [hX'], by rw [hX'],
      by rw [hX'], hbs, fun c C0 C hC0 hC => ?_, fun c => ?_, [], trivial, rfl, fun _ h => by cases h⟩
    · rw [hnl', GMap.lookup_insert_ne _ _ (fun he => by rw [← he, hnl] at hxy; cases hxy)]
      exact hxy
    · rw [hbsX] at hC; split at hC
      · rename_i hcb; subst hcb; rw [hb] at hC0; cases hC0; cases hC; exact ⟨rfl, rfl, rfl⟩
      · rw [hC0] at hC; cases hC; exact ⟨rfl, rfl, rfl⟩
    · rw [List.map_flatten, List.map_flatten, hleaves c]
  · -- the unbalanced nodes
    intro B2 B2' hB2 hB2' y ry' hy hu
    rw [hb] at hB2; cases hB2
    rw [hB'] at hB2'; cases hB2'
    exact hunb1 y ry' hy hu

end mat

end bbolt
end EtcdGrove
end Perennial
