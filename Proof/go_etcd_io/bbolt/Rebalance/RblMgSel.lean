/-
`node.rebalance`'s merge (U8e): the sibling selected (`n.nextSibling()`/`n.prevSibling()`, cached or
materialized: `rblX_sibMat`, `rblX_colMat` for any entry of any branch node and any deficient node),
the merge's nodes and their moved children (`mg_kids`), the bucket right after the merge's code
before the right node is freed (`mgBktL`, its records `mgF`, `mgBktL_close`), and the steps
composed (`rblPre_mg`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXMg
public import Proof.go_etcd_io.bbolt.Rebalance.RblColMat
public import Proof.go_etcd_io.bbolt.Rebalance.NodeRblBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section mgsel
variable [GooseExts]

/-- **A branch node's child materialized** (`Bucket.node`, or a sibling, of the branch `p`'s entry
`i`): the bucket after, the child's record, the invariant kept, the other nodes' records kept. -/
theorem rblX_sibMat (X1 X2 : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (B1 : BRec) (p : Loc)
    (r1 : NRec) (i : Nat) (w0 : WEntry) (lc : Loc)
    (hI : rblX X1 fl bl dfc) (hb : X1.t.bs !! bl = some B1) (hr : B1.ns !! p = some r1)
    (hbr : r1.nv.isLeaf' = false) (hw : r1.ws[i]? = some w0)
    (hmat : (B1.nm !! w0.pgid = some lc ∧ X2 = X1) ∨ nodeAdded X1 X2 bl lc w0.pgid p)
    (hnl : (X1.t.objs !! lc).isNone → X1.nloc !! lc = none) :
    ∃ B2 r2 rc, X2.t.bs !! bl = some B2 ∧ B2.ns !! p = some r2 ∧ B2.nm !! w0.pgid = some lc ∧
      B2.ns !! lc = some rc ∧ rblX X2 fl bl dfc ∧ rblRel X1 fl X2 fl X1.t.mv.txid' ∧
      (∀ bl', bl' ≠ bl → X2.t.bs !! bl' = X1.t.bs !! bl') ∧
      r2.nv = { r1.nv with children' := r2.nv.children' } ∧ r2.ws = r1.ws ∧ r2.ins = r1.ins ∧
      r2.key = r1.key ∧ r2.ksrc = r1.ksrc ∧ r2.capOwn = r1.capOwn ∧
      (∀ y ry, y ≠ p → B1.ns !! y = some ry → B2.ns !! y = some ry) ∧
      (∀ c l, B1.nm !! c = some l → B2.nm !! c = some l) ∧
      (∀ y ry', B2.ns !! y = some ry' → ry'.nv.unbalanced' = true →
        ∃ ry, B1.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid') := by
  have hB := (hI.2.1 bl B1 hb).1
  have hc : bktClean X1.v X1.t.mv.pgid'.toNat bl B1 := hB.1
  rcases hmat with ⟨hlc, rfl⟩ | hadd
  · obtain ⟨-, rc, hrc, -⟩ := hc.2.2.2.2.1 _ _ hlc
    exact ⟨B1, r1, rc, hb, hr, hlc, hrc, hI, rblRel_refl _ _ _, fun _ _ => rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, fun _ _ _ h => h, fun _ _ h => h, fun y ry' hy hu => ⟨ry', hy, hu, rfl⟩⟩
  have hadd' := hadd
  obtain ⟨B0, pa, pg, r, ns', bv', hB0, -, hnone, -, hobj, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hcase, hX'⟩ := hadd'
  rw [hb] at hB0; cases hB0
  have hpos : ∃ B, X1.t.bs !! bl = some B ∧ pagePosAt B p i w0.pgid :=
    ⟨B1, hb, r1, w0, hr, hbr, hw, rfl, hnone⟩
  obtain ⟨hI2, hR2, hU2⟩ := rblX_mat X1 X2 fl bl dfc lc w0.pgid p i hI hadd hpos (hnl hobj)
  have hnn : p ≠ null := (hc.2.2.2.2.1 _ _ (ncol_nm (hc.2.2.2.2.2.2.2.1 p r1 hr))).1
  have hlcn : lc ≠ p := by
    intro he; subst he
    have := (objs_isSome X1.t lc).2 (Or.inr ⟨bl, B1, hb, by rw [hr]; rfl⟩)
    rw [Option.isNone_iff_eq_none] at hobj; rw [hobj] at this; cases this
  rcases hcase with ⟨hpn, -, -⟩ | ⟨-, hbv, rp0, rp', hrp0, -, hc1, hc2, hc3, hc4, hc5, hcp, hc6, hns⟩
  · exact absurd hpn hnn
  rw [hr] at hrp0; cases hrp0
  subst hbv; subst hns
  have hb2 : X2.t.bs !! bl =
      some { B1 with nm := B1.nm.insert w0.pgid lc, ns := (B1.ns.insert p rp').insert lc r } := by
    rw [hX']; exact GMap.lookup_insert _ _ _
  refine ⟨_, rp', r, hb2, ?_, GMap.lookup_insert _ _ _, GMap.lookup_insert _ _ _, hI2, hR2, ?_, hc6,
    hc2, hc3, hc4, hc5, hcp, fun y ry h1 hy => ?_, fun c l h => ?_, hU2 B1 _ hb hb2⟩
  · show ((B1.ns.insert p rp').insert lc r) !! p = _
    rw [GMap.lookup_insert_ne _ _ hlcn]; exact GMap.lookup_insert _ _ _
  · intro bl' hne
    rw [hX']; exact GMap.lookup_insert_ne _ _ (Ne.symm hne)
  · have h2 : y ≠ lc := by
      intro he; subst he
      have := (objs_isSome X1.t y).2 (Or.inr ⟨bl, B1, hb, by rw [hy]; rfl⟩)
      rw [Option.isNone_iff_eq_none] at hobj; rw [hobj] at this; cases this
    show ((B1.ns.insert p rp').insert lc r) !! y = _
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h2), GMap.lookup_insert_ne _ _ (Ne.symm h1)]; exact hy
  · show (B1.nm.insert w0.pgid lc) !! c = _
    have hcne : w0.pgid ≠ c := by intro he; subst he; rw [hnone] at h; cases h
    rw [GMap.lookup_insert_ne _ _ hcne]; exact h

/-- **The merge's nodes** (the parent `pl`, the siblings `ll`, `lr`) and the right node's moved
children (`kidsOf` of its entries: the nodes whose parent is `lr`), without repetition. -/
theorem mg_kids (X : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (B : BRec) (pl : Loc) (rp : NRec)
    (k : Nat) (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec)
    (hI : rblX X fl bl dfc) (hb : X.t.bs !! bl = some B)
    (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp) (hbr : rp.nv.isLeaf' = false)
    (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
    (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
    (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr) :
    (∀ c, c ∈ kidsOf B rr.ws ↔ ∃ rk, B.ns !! c = some rk ∧ rk.nv.parent' = lr) ∧
      ([pl, ll, lr] ++ kidsOf B rr.ws).Nodup ∧
      (∀ c ∈ kidsOf B rr.ws, c ≠ pl ∧ c ≠ ll ∧ c ≠ lr) := by
  have hV : viewWF X.v := hI.2.2.2.2.2.2.1
  have hrb := (hI.2.1 bl B hb).1
  rw [if_pos rfl] at hrb
  obtain ⟨hc, ⟨bnd, hk⟩, ha, -⟩ := hrb
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, -, -, -, -, h0, -⟩ :=
    mg_basic X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hp00 : X.v.pages !! 0 = none := by
    cases h : X.v.pages !! 0 with
    | none => rfl
    | some pg0 => have := (Read.viewWF_page X.v hV 0 pg0 h).1; omega
  have hleaf0 : rr.nv.isLeaf' = true → ∀ w ∈ rr.ws, B.nm !! w.pgid = none := by
    intro hl w hw
    have h0' := ((hk.2.2 lr rr hrr).2.2.2.2 hl w hw).1
    rw [h0']
    cases hn0 : B.nm !! W64 0 with
    | none => rfl
    | some l0 =>
      obtain ⟨-, r0, hr0, hpg0⟩ := hc.2.2.2.2.1 _ _ hn0
      have hwf := (hc.2.2.2.2.2.2.2.1 l0 r0 hr0).2.2.2.2.2.2.2.2.2.1 h0
      rw [hpg0] at hwf
      cases hwf with
      | page _ pg _ _ hpg _ _ _ => rw [show (W64 0).toNat = 0 from rfl, hp00] at hpg; cases hpg
  obtain ⟨hchar, hnd⟩ := mg_moved X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr
    hrl hrr hleaf0
  have hpk : pl ∉ kidsOf B rr.ws := fun h => by
    obtain ⟨rk, hrk, hpk⟩ := (hchar pl).1 h
    exact mg_cyc X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
      pl rk hrk (Or.inr hpk) rfl
  have hlk : ll ∉ kidsOf B rr.ws := fun h => by
    obtain ⟨rk, hrk, hpk⟩ := (hchar ll).1 h
    rw [hrl] at hrk; cases hrk; rw [hp1] at hpk; exact hlrp hpk.symm
  have hrk : lr ∉ kidsOf B rr.ws := fun h => by
    obtain ⟨rk, hrk, hpk⟩ := (hchar lr).1 h
    rw [hrr] at hrk; cases hrk; rw [hp2] at hpk; exact hlrp hpk.symm
  refine ⟨hchar, ?_, fun c hcm => ⟨fun h => hpk (h ▸ hcm), fun h => hlk (h ▸ hcm),
    fun h => hrk (h ▸ hcm)⟩⟩
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, not_or]
  exact ⟨⟨Ne.symm hllp, Ne.symm hlrp, hpk⟩, ⟨hllr, hlk⟩, hrk, hnd⟩

theorem kidsOf_take_succ_eq (B : BRec) (ws : List WEntry) (j : Nat) (w : WEntry)
    (hw : ws[j]? = some w) :
    kidsOf B (ws.take (j + 1)) = kidsOf B (ws.take j) ++ (B.nm !! w.pgid).toList := by
  unfold kidsOf
  rw [List.take_succ, hw, List.filterMap_append]
  simp only [Option.toList_some, List.filterMap_cons, List.filterMap_nil]
  cases B.nm !! w.pgid <;> rfl

/-- The merge's loop reaches each moved child once: at its entry, not yet reparented. -/
theorem colKid_fresh (B : BRec) (ws : List WEntry) (nl : Loc) (dflt : NRec) (j : Nat) (w : WEntry)
    (k : Loc) (hnd : (kidsOf B ws).Nodup) (hw : ws[j]? = some w) (hk : B.nm !! w.pgid = some k) :
    colKid B ws nl dflt j k = (B.ns !! k).getD dflt := by
  unfold colKid
  rw [if_neg]
  intro hm
  have hsplit : kidsOf B ws = kidsOf B (ws.take (j + 1)) ++ kidsOf B (ws.drop (j + 1)) := by
    unfold kidsOf; rw [← List.filterMap_append, List.take_append_drop]
  rw [hsplit, kidsOf_take_succ_eq B ws j w hw, hk] at hnd
  have := (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2
  simp only [Option.toList_some, List.mem_singleton] at this
  exact this k hm k rfl rfl

/-- The right node after the merge's code, before its page is freed (its children slice `sCr` and
list `csr`: the loop's `removeChild`s). -/
def mgR (rr : NRec) (sCr : GoSlice) (csr : List Loc) : NRec :=
  { rr with nv := { rr.nv with children' := sCr }, cs := csr }

/-- The bucket after the merge's code, the right node `lr` still a node (`mgR`), before its page
is freed and it goes dead (`mgBktX` then, by `WX.kill`). -/
def mgBktL (B : BRec) (pl : Loc) (rp : NRec) (k : Nat) (ll lr : Loc) (rl rr : NRec)
    (sI sC sI' sC' sCr : GoSlice) (csr : List Loc) : BRec :=
  { mgBktX B pl rp k ll lr rl rr sI sC sI' sC' with
    ns := (mgBktX B pl rp k ll lr rl rr sI sC sI' sC').ns.insert lr (mgR rr sCr csr) }

/-- The records of the parent, the siblings and the moved children after the merge's code. -/
def mgF (B : BRec) (pl : Loc) (rp : NRec) (k : Nat) (ll lr : Loc) (rl rr : NRec)
    (sI sC sI' sC' sCr : GoSlice) (csr : List Loc) (l : Loc) : NRec :=
  if l = pl then mgParent rp (k + 1) lr sI' sC' else
  if l = ll then mgLeft rl rr (kidsOf B rr.ws) sI sC else
  if l = lr then mgR rr sCr csr else colKid B rr.ws ll rr rr.ws.length l

/-- **Closing the heap after the merge's code** (`wtxHeap_setBkt_live_acc`'s premises). -/
theorem mgBktL_close (B : BRec) (pl : Loc) (rp : NRec) (k : Nat) (ll lr : Loc) (rl rr : NRec)
    (sI sC sI' sC' sCr : GoSlice) (csr : List Loc)
    (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr)
    (hp1 : rl.nv.parent' = pl) (hp2 : rr.nv.parent' = pl) (hpp : rp.nv.parent' ≠ pl)
    (hllp : ll ≠ pl) (hlrp : lr ≠ pl) (hllr : ll ≠ lr)
    (hchar : ∀ c, c ∈ kidsOf B rr.ws ↔ ∃ rk, B.ns !! c = some rk ∧ rk.nv.parent' = lr)
    (hkn : ∀ c ∈ kidsOf B rr.ws, c ≠ pl ∧ c ≠ ll ∧ c ≠ lr) :
    (∀ l ∈ [pl, ll, lr] ++ kidsOf B rr.ws,
      (mgBktL B pl rp k ll lr rl rr sI sC sI' sC' sCr csr).ns !! l =
        some (mgF B pl rp k ll lr rl rr sI sC sI' sC' sCr csr l)) ∧
    (∀ l, l ∉ [pl, ll, lr] ++ kidsOf B rr.ws →
      (mgBktL B pl rp k ll lr rl rr sI sC sI' sC' sCr csr).ns !! l = B.ns !! l) ∧
    (∀ l ∈ [pl, ll, lr] ++ kidsOf B rr.ws,
      (mgF B pl rp k ll lr rl rr sI sC sI' sC' sCr csr l).nv.parent' ≠ l) := by
  have hns : ∀ l, (mgBktL B pl rp k ll lr rl rr sI sC sI' sC' sCr csr).ns !! l =
      if l = lr then some (mgR rr sCr csr) else
        (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
          (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! l := by
    intro l
    show ((mgBkt B pl ll lr rr.nv.pgid' _ _).ns.insert lr _) !! l = _
    split
    · rename_i h; subst h; exact GMap.lookup_insert _ _ _
    · exact GMap.lookup_insert_ne _ _ (Ne.symm ‹_›)
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons] at hl
    rcases hl with rfl | rfl | rfl | hl
    · rw [hns, if_neg (Ne.symm hlrp), mg_ns, if_pos rfl]; unfold mgF; rw [if_pos rfl]
    · rw [hns, if_neg hllr, mg_ns, if_neg hllp, if_pos rfl]; unfold mgF
      rw [if_neg hllp, if_pos rfl]
    · rw [hns, if_pos rfl]; unfold mgF; rw [if_neg hlrp, if_neg (Ne.symm hllr), if_pos rfl]
    · obtain ⟨h1, h2, h3⟩ := hkn l hl
      obtain ⟨rk, hrk, hpk⟩ := (hchar l).1 hl
      rw [hns, if_neg h3, mg_ns, if_neg h1, if_neg h2, if_neg h3, hrk]
      unfold mgF; rw [if_neg h1, if_neg h2, if_neg h3, colKid_all _ _ _ _ _ hl, hrk]
      simp only [Option.map_some, hpk, ite_true, Option.getD_some]; rfl
  · simp only [List.cons_append, List.nil_append, List.mem_cons, not_or] at hl
    obtain ⟨h1, h2, h3, h4⟩ := hl
    rw [hns, if_neg h3, mg_ns, if_neg h1, if_neg h2, if_neg h3]
    cases hy : B.ns !! l with
    | none => rfl
    | some ry =>
      simp only [Option.map_some, Option.some.injEq]
      rw [if_neg (fun hp => h4 ((hchar l).2 ⟨ry, hy, hp⟩))]
  · simp only [List.cons_append, List.nil_append, List.mem_cons] at hl
    rcases hl with rfl | rfl | rfl | hl
    · unfold mgF; rw [if_pos rfl]; exact hpp
    · unfold mgF; rw [if_neg hllp, if_pos rfl]; show rl.nv.parent' ≠ _; rw [hp1]; exact Ne.symm hllp
    · unfold mgF; rw [if_neg hlrp, if_neg (Ne.symm hllr), if_pos rfl]; show rr.nv.parent' ≠ _
      rw [hp2]; exact Ne.symm hlrp
    · obtain ⟨h1, h2, h3⟩ := hkn l hl
      unfold mgF; rw [if_neg h1, if_neg h2, if_neg h3, colKid_all _ _ _ _ _ hl]; exact Ne.symm h2

/-- The right node's key: its parent's entry `k + 1`, found there. -/
theorem mg_rkey (X : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (B : BRec) (pl : Loc) (rp : NRec)
    (k : Nat) (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec)
    (hI : rblX X fl bl dfc) (hb : X.t.bs !! bl = some B)
    (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp) (hbr : rp.nv.isLeaf' = false)
    (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
    (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
    (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr) :
    rr.nv.key' ≠ slice.nil ∧ rr.ksrc ≠ Src.stale ∧ wsIdx rp.ws rr.key = k + 1 ∧
      wsFound rp.ws rr.key ∧ wsDelAt rp.ws rr.key = rp.ws.eraseIdx (k + 1) := by
  have hrb := (hI.2.1 bl B hb).1
  rw [if_pos rfl] at hrb
  obtain ⟨hc, ⟨bnd, hk⟩, ha, -⟩ := hrb
  obtain ⟨-, hp2, -, -, -, -, hpgr, -, hnd, -⟩ :=
    mg_basic X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  obtain ⟨hkey, rq, i, wi, hrq, hwi, hwp, hwk, -⟩ := (hk.2.2 lr rr hrr).2.1 (by rw [hp2]; exact hpn)
  rw [hp2, hrp] at hrq; cases hrq
  have hi : i = k + 1 := by
    by_cases h : i = k + 1
    · exact h
    · exact absurd (hwp.trans hpgr).symm (nodup_pgid_ne_mg rp.ws hnd i (k + 1) wi wr hwi hwr (Ne.symm h))
  subst hi
  have hncp := hc.2.2.2.2.2.2.2.1 pl rp hrp
  have hn1 := hc.2.2.2.2.2.2.2.1 lr rr hrr
  have hks : rr.ksrc ≠ Src.stale := (hn1.2.2.2.2.2.2.2.2.2.2.1.resolve_left hkey).2
  have hfound := wsDelAt_at rp.ws (k + 1) wi hncp.2.2.2.1 hwi
  have hidx := wsIdx_at rp.ws (k + 1) wi hncp.2.2.2.1 hwi
  rw [hwk] at hfound hidx
  exact ⟨hkey, hks, hidx, hfound.1, hfound.2⟩

/-- **The merge's steps composed** (`rblStart`, the sibling's materialization, the merge): before
the parent's rebalance, `rblPre`. -/
theorem rblPre_mg (B B2 BX : BRec) (n pl lr : Loc) (rn : NRec)
    (he : B2.bv = (rblStart B n rn).bv ∧ B2.ib = (rblStart B n rn).ib ∧ B2.bm = (rblStart B n rn).bm)
    (hU2 : ∀ y ry', B2.ns !! y = some ry' → ry'.nv.unbalanced' = true →
      ∃ ry, (rblStart B n rn).ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
        ry'.nv.pgid' = ry.nv.pgid')
    (hX : BX.bv = B2.bv ∧ BX.ib = B2.ib ∧ BX.bm = B2.bm)
    (hU : ∀ y ry', BX.ns !! y = some ry' → ry'.nv.unbalanced' = true →
      y = pl ∨ (y ≠ lr ∧ ∃ ry, B2.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
        ry'.nv.pgid' = ry.nv.pgid')) :
    rblPre B BX n pl := by
  refine ⟨hX.1.trans he.1, hX.2.1.trans he.2.1, hX.2.2.trans he.2.2, fun y ry' hy hu => ?_⟩
  rcases hU y ry' hy hu with h | ⟨-, ry2, hy2, hu2, hp2⟩
  · exact Or.inl h
  obtain ⟨ry1, hy1, hu1, hp1⟩ := hU2 y ry2 hy2 hu2
  change (<[n := rblClear rn]> B.ns) !! y = some ry1 at hy1
  rw [rf_lookup] at hy1
  split at hy1
  · cases hy1; cases hu1
  · rename_i hyn
    exact Or.inr ⟨hyn, ry1, hy1, hu1, hp2.trans hp1⟩

end mgsel

end bbolt
end EtcdGrove
end Perennial
