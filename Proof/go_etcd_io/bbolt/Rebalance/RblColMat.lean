/-
The root's only child materialized before the collapse (`n.bucket.node(n.inodes[0].Pgid(), n)` in
`node.rebalance`, U8d): from `Bucket.node`'s postcondition (cached, or `nodeAdded`), the bucket after
with the child's record, the invariant kept (`rblX_mat`), and the root's record after (its children
slice may have grown).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSteps
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSMat
public import Proof.go_etcd_io.bbolt.Rebalance.RblMg1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section colmat
variable [GooseExts]

/-- **The root's child materialized** (`Bucket.node` of the root `n`'s only entry `w0`). -/
theorem rblX_colMat (X1 X2 : WX) (fl : FLPg) (bl : Loc) (B1 : BRec) (n : Loc) (r1 : NRec)
    (w0 : WEntry) (lc : Loc)
    (hI : rblX X1 fl bl (some n)) (hb : X1.t.bs !! bl = some B1) (hr : B1.ns !! n = some r1)
    (hbr : r1.nv.isLeaf' = false) (hws : r1.ws = [w0])
    (hmat : (B1.nm !! w0.pgid = some lc ∧ X2 = X1) ∨ nodeAdded X1 X2 bl lc w0.pgid n)
    (hnl : (X1.t.objs !! lc).isNone → X1.nloc !! lc = none) :
    ∃ B2 r2 rc, X2.t.bs !! bl = some B2 ∧ B2.ns !! n = some r2 ∧ B2.nm !! w0.pgid = some lc ∧
      B2.ns !! lc = some rc ∧ rblX X2 fl bl (some n) ∧ rblRel X1 fl X2 fl X1.t.mv.txid' ∧
      (∀ bl', bl' ≠ bl → X2.t.bs !! bl' = X1.t.bs !! bl') ∧
      r2.nv = { r1.nv with children' := r2.nv.children' } ∧ r2.ws = r1.ws ∧ r2.ins = r1.ins ∧
      r2.key = r1.key ∧ r2.ksrc = r1.ksrc ∧ r2.capOwn = r1.capOwn ∧
      (∀ y ry', B2.ns !! y = some ry' → ry'.nv.unbalanced' = true →
        ∃ ry, B1.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid') := by
  have hB := (hI.2.1 bl B1 hb).1
  rw [if_pos rfl] at hB
  have hc := hB.1
  rcases hmat with ⟨hlc, rfl⟩ | hadd
  · obtain ⟨-, rc, hrc, -⟩ := hc.2.2.2.2.1 _ _ hlc
    exact ⟨B1, r1, rc, hb, hr, hlc, hrc, hI, rblRel_refl _ _ _, fun _ _ => rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, fun y ry' hy hu => ⟨ry', hy, hu, rfl⟩⟩
  have hadd' := hadd
  obtain ⟨B0, pa, pg, r, ns', bv', hB0, -, hnone, -, hobj, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hcase, hX'⟩ := hadd'
  rw [hb] at hB0; cases hB0
  have hpos : ∃ B, X1.t.bs !! bl = some B ∧ pagePosAt B n 0 w0.pgid :=
    ⟨B1, hb, r1, w0, hr, hbr, by rw [hws]; rfl, rfl, hnone⟩
  obtain ⟨hI2, hR2, hU2⟩ := rblX_mat X1 X2 fl bl (some n) lc w0.pgid n 0 hI hadd hpos (hnl hobj)
  have hnn : n ≠ null := (hc.2.2.2.2.1 _ _ (ncol_nm (hc.2.2.2.2.2.2.2.1 n r1 hr))).1
  have hlcn : lc ≠ n := by
    intro he; subst he
    have := (objs_isSome X1.t lc).2 (Or.inr ⟨bl, B1, hb, by rw [hr]; rfl⟩)
    rw [Option.isNone_iff_eq_none] at hobj; rw [hobj] at this; cases this
  rcases hcase with ⟨hpn, -, -⟩ | ⟨-, hbv, rp0, rp', hrp0, -, hc1, hc2, hc3, hc4, hc5, hcp, hc6, hns⟩
  · exact absurd hpn hnn
  rw [hr] at hrp0; cases hrp0
  subst hbv; subst hns
  have hb2 : X2.t.bs !! bl =
      some { B1 with nm := B1.nm.insert w0.pgid lc, ns := (B1.ns.insert n rp').insert lc r } := by
    rw [hX']; exact GMap.lookup_insert _ _ _
  refine ⟨_, rp', r, hb2, ?_, GMap.lookup_insert _ _ _, GMap.lookup_insert _ _ _, hI2, hR2, ?_, hc6,
    hc2, hc3, hc4, hc5, hcp, hU2 B1 _ hb hb2⟩
  · show ((B1.ns.insert n rp').insert lc r) !! n = _
    rw [GMap.lookup_insert_ne _ _ hlcn]; exact GMap.lookup_insert _ _ _
  · intro bl' hne
    rw [hX']; exact GMap.lookup_insert_ne _ _ (Ne.symm hne)

/-- A node record with its parent `p`. -/
def colRe (r : NRec) (p : Loc) : NRec := { r with nv := { r.nv with parent' := p } }

/-- The collapse's reparenting loop after `j` entries of the child's `ws`: the nodes found so far
(`kidsOf B (ws.take j)`) have the parent `nl` (`dflt` stands for a location with no record). -/
def colKid (B : BRec) (ws : List WEntry) (nl : Loc) (dflt : NRec) (j : Nat) (k : Loc) : NRec :=
  if k ∈ kidsOf B (ws.take j) then colRe ((B.ns !! k).getD dflt) nl else (B.ns !! k).getD dflt

theorem colKid_zero (B : BRec) (ws : List WEntry) (nl : Loc) (dflt : NRec) (k : Loc) :
    colKid B ws nl dflt 0 k = (B.ns !! k).getD dflt := by
  unfold colKid; rw [if_neg]; simp [kidsOf]

theorem colKid_all (B : BRec) (ws : List WEntry) (nl : Loc) (dflt : NRec) (k : Loc)
    (hk : k ∈ kidsOf B ws) : colKid B ws nl dflt ws.length k = colRe ((B.ns !! k).getD dflt) nl := by
  unfold colKid; rw [List.take_length, if_pos hk]

theorem kidsOf_take_succ (B : BRec) (ws : List WEntry) (j : Nat) (w : WEntry)
    (hw : ws[j]? = some w) (k : Loc) :
    k ∈ kidsOf B (ws.take (j + 1)) ↔ k ∈ kidsOf B (ws.take j) ∨ B.nm !! w.pgid = some k := by
  unfold kidsOf
  rw [List.take_succ, hw, List.filterMap_append, List.mem_append]
  simp only [Option.toList_some, List.filterMap_cons, List.filterMap_nil]
  cases h : B.nm !! w.pgid with
  | none => simp
  | some x => simp [eq_comm]

/-- An entry naming no node leaves the loop's records. -/
theorem colKid_none (B : BRec) (ws : List WEntry) (nl : Loc) (dflt : NRec) (j : Nat) (w : WEntry)
    (hw : ws[j]? = some w) (hn : B.nm !! w.pgid = none) (k : Loc) :
    colKid B ws nl dflt (j + 1) k = colKid B ws nl dflt j k := by
  unfold colKid
  have := kidsOf_take_succ B ws j w hw k
  rw [hn] at this; simp only [reduceCtorEq, _root_.or_false] at this
  by_cases h : k ∈ kidsOf B (ws.take j)
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]

/-- An entry naming the node `k0`: `k0` reparented, the others unchanged. -/
theorem colKid_some (B : BRec) (ws : List WEntry) (nl : Loc) (dflt : NRec) (j : Nat) (w : WEntry)
    (hw : ws[j]? = some w) (k0 : Loc) (hn : B.nm !! w.pgid = some k0) :
    colKid B ws nl dflt (j + 1) k0 = colRe (colKid B ws nl dflt j k0) nl ∧
    ∀ k, k ≠ k0 → colKid B ws nl dflt (j + 1) k = colKid B ws nl dflt j k := by
  have hs := kidsOf_take_succ B ws j w hw
  refine ⟨?_, fun k hk => ?_⟩
  · unfold colKid
    rw [if_pos ((hs k0).2 (Or.inr hn))]
    split <;> rfl
  · unfold colKid
    have h1 := hs k
    rw [hn] at h1
    have h2 : B.nm !! w.pgid = some k ↔ False := by
      rw [hn]; simp only [Option.some.injEq, iff_false]; exact fun h => hk h.symm
    by_cases h : k ∈ kidsOf B (ws.take j)
    · rw [if_pos (h1.2 (Or.inl h)), if_pos h]
    · rw [if_neg (fun h' => by rcases h1.1 h' with h3 | h3; exact h h3; exact hk (Option.some.inj h3).symm),
        if_neg h]

/-- **The collapsed child's children** (`kidsOf` of its entries): the nodes whose parent is the
child, without repetition, apart from the root and the child. -/
theorem col_kids (X : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (B : BRec) (nl : Loc)
    (rn : NRec) (w0 : WEntry) (lc : Loc) (rc : NRec)
    (hI : rblX X fl bl dfc) (hb : X.t.bs !! bl = some B) (hrn : B.ns !! nl = some rn)
    (hbr : rn.nv.isLeaf' = false) (hpn : rn.nv.parent' = null) (hws : rn.ws = [w0])
    (hlc : B.nm !! w0.pgid = some lc) (hrc : B.ns !! lc = some rc) :
    (∀ c, c ∈ kidsOf B rc.ws ↔ ∃ rk, B.ns !! c = some rk ∧ rk.nv.parent' = lc) ∧
      ([nl, lc] ++ kidsOf B rc.ws).Nodup ∧ (∀ c ∈ kidsOf B rc.ws, c ≠ nl ∧ c ≠ lc) := by
  have hB := (hI.2.1 bl B hb).1
  rw [if_pos rfl] at hB
  obtain ⟨hc, ⟨bnd, hk⟩, ha, -⟩ := hB
  have hV : viewWF X.v := hI.2.2.2.2.2.2.1
  obtain ⟨hp1, hlcn, -, -, -, h0, -⟩ :=
    col_basic X.v _ bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  have hp00 : X.v.pages !! 0 = none := by
    cases h : X.v.pages !! 0 with
    | none => rfl
    | some pg0 => have := (Read.viewWF_page X.v hV 0 pg0 h).1; omega
  have hleaf0 : rc.nv.isLeaf' = true → ∀ w ∈ rc.ws, B.nm !! w.pgid = none := by
    intro hl w hw
    have h0' := ((hk.2.2 lc rc hrc).2.2.2.2 hl w hw).1
    rw [h0']
    cases hn0 : B.nm !! W64 0 with
    | none => rfl
    | some l0 =>
      obtain ⟨-, r0, hr0, hpg0⟩ := hc.2.2.2.2.1 _ _ hn0
      have hwf := (hc.2.2.2.2.2.2.2.1 l0 r0 hr0).2.2.2.2.2.2.2.2.2.1 h0
      rw [hpg0] at hwf
      cases hwf with
      | page _ pg _ _ hpg _ _ _ => rw [show (W64 0).toNat = 0 from rfl, hp00] at hpg; cases hpg
  have hlcnull : lc ≠ null := (hc.2.2.2.2.1 _ _ hlc).1
  have hnr := hc.2.2.2.2.2.2.2.1 lc rc hrc
  have hchar : ∀ c, c ∈ kidsOf B rc.ws ↔ ∃ rk, B.ns !! c = some rk ∧ rk.nv.parent' = lc := by
    intro c
    refine ⟨fun hcm => ?_, fun ⟨rk, hrk, hpk⟩ => ?_⟩
    · obtain ⟨x, hx, hxc⟩ := List.mem_filterMap.1 hcm
      rcases (Bool.eq_false_or_eq_true rc.nv.isLeaf').symm with hb' | hb'
      · obtain ⟨-, -, hkk⟩ := ncol_br hnr hb'
        exact (hkk x hx).2.1 c hxc
      · rw [hleaf0 hb' x hx] at hxc; cases hxc
    · have hcn := hc.2.2.2.2.2.2.2.1 c rk hrk
      obtain ⟨rq, hrq, -, -, x, hx, hxp⟩ := ncol_par hcn (by rw [hpk]; exact hlcnull)
      rw [hpk, hrc] at hrq; cases hrq
      exact List.mem_filterMap.2 ⟨x, hx, by rw [hxp]; exact ncol_nm hcn⟩
  have hnd : (kidsOf B rc.ws).Nodup := by
    rcases (Bool.eq_false_or_eq_true rc.nv.isLeaf').symm with hb' | hb'
    · obtain ⟨-, hnd, -⟩ := ncol_br hnr hb'
      unfold kidsOf
      have key : ∀ (l : List WEntry), (l.map WEntry.pgid).Nodup →
          (l.filterMap fun w => B.nm !! w.pgid).Nodup := by
        intro l
        induction l with
        | nil => intro _; exact List.nodup_nil
        | cons x xs ih =>
          intro hn
          rw [List.map_cons, List.nodup_cons] at hn
          rw [List.filterMap_cons]
          cases hx : B.nm !! x.pgid with
          | none => exact ih hn.2
          | some b =>
            refine List.nodup_cons.2 ⟨fun hb'' => ?_, ih hn.2⟩
            obtain ⟨y, hy, hyb⟩ := List.mem_filterMap.1 hb''
            have := col_nm_inj X.v _ bl B hc _ _ _ hx hyb
            exact hn.1 (List.mem_map.2 ⟨y, hy, this.symm⟩)
      exact key _ hnd
    · have : kidsOf B rc.ws = [] := by
        unfold kidsOf; rw [List.filterMap_eq_nil_iff]; exact hleaf0 hb'
      rw [this]; exact List.nodup_nil
  have hn : nl ∉ kidsOf B rc.ws := fun h => by
    obtain ⟨rk, hrk, hpk⟩ := (hchar nl).1 h
    rw [hrn] at hrk; cases hrk; rw [hpn] at hpk; exact hlcnull hpk.symm
  have hl : lc ∉ kidsOf B rc.ws := fun h => by
    obtain ⟨rk, hrk, hpk⟩ := (hchar lc).1 h
    rw [hrc] at hrk; cases hrk; rw [hp1] at hpk; exact hlcn hpk.symm
  refine ⟨hchar, ?_, fun c hcm => ⟨fun h => hn (h ▸ hcm), fun h => hl (h ▸ hcm)⟩⟩
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, not_or]
  exact ⟨⟨Ne.symm hlcn, hn⟩, hl, hnd⟩

/-- **The collapse's steps composed** (`rblStart`, the child's materialization, the collapse
`rblX_col`): the steps' relation, the other buckets unchanged, `n` no longer unbalanced and no
node newly so. -/
theorem rbl_col_post (X X2 : WX) (fl fl' : FLPg) (bl : Loc) (B B2 Bc : BRec) (n lc : Loc)
    (rn rn2 rcf : NRec) (hb : X.t.bs !! bl = some B)
    (hR1 : rblRel X fl (X.setBkt bl (rblStart B n rn)) fl X.t.mv.txid')
    (hR2 : rblRel (X.setBkt bl (rblStart B n rn)) fl X2 fl X.t.mv.txid')
    (hb2 : X2.t.bs !! bl = some B2)
    (hoth2 : ∀ bl', bl' ≠ bl → X2.t.bs !! bl' = (X.setBkt bl (rblStart B n rn)).t.bs !! bl')
    (hU2 : ∀ y ry', B2.ns !! y = some ry' → ry'.nv.unbalanced' = true →
      ∃ ry, (rblStart B n rn).ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
        ry'.nv.pgid' = ry.nv.pgid')
    (hun2 : rn2.nv.unbalanced' = false)
    (hRc : rblRel X2 fl (X2.kill bl Bc lc rcf) fl' X2.t.mv.txid')
    (hUc : ∀ y ry', Bc.ns !! y = some ry' → ry'.nv.unbalanced' = true →
      y = n ∧ rn2.nv.unbalanced' = true ∨ (y ≠ lc ∧ ∃ ry, B2.ns !! y = some ry ∧
        ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid'))
    (hbc : Bc.bv = B2.bv ∧ Bc.ib = B2.ib ∧ Bc.bm = B2.bm) :
    rblRel X fl (X2.kill bl Bc lc rcf) fl' X.t.mv.txid' ∧
      (∀ bl', bl' ≠ bl → (X2.kill bl Bc lc rcf).t.bs !! bl' = X.t.bs !! bl') ∧ rblStep B Bc n := by
  have hmv : X2.t.mv = X.t.mv := hR2.2.2.2.2.2.1
  rw [hmv] at hRc
  have hb1 : (X.setBkt bl (rblStart B n rn)).t.bs !! bl = some (rblStart B n rn) :=
    GMap.lookup_insert _ _ _
  obtain ⟨e1, e2, e3⟩ := hR2.2.2.2.2.2.2.2.2.2.1 bl _ B2 hb1 hb2
  refine ⟨rblRel_trans _ _ _ _ _ _ _ hR1 (rblRel_trans _ _ _ _ _ _ _ hR2 hRc), fun bl' hne => ?_,
    hbc.1.trans e1, hbc.2.1.trans e2, hbc.2.2.trans e3, fun y ry' hy hu => ?_⟩
  · show (X2.t.bs.insert bl Bc) !! bl' = _
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne), hoth2 bl' hne]
    show (X.t.bs.insert bl _) !! bl' = _
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]
  rcases hUc y ry' hy hu with ⟨-, h⟩ | ⟨-, ry2, hy2, hu2, hp2⟩
  · rw [hun2] at h; cases h
  obtain ⟨ry1, hy1, hu1, hp1⟩ := hU2 y ry2 hy2 hu2
  change (<[n := rblClear rn]> B.ns) !! y = some ry1 at hy1
  rw [rf_lookup] at hy1
  split at hy1
  · cases hy1; cases hu1
  · rename_i hyn
    exact ⟨hyn, ry1, hy1, hu1, hp2.trans hp1⟩

/-- The bucket after the collapse's field moves, the child `lc` still a node (its parent nil),
before its page is freed and it goes dead (`colBkt` then, by `WX.kill`). -/
def colBktL (B : BRec) (nl lc : Loc) (rn rc : NRec) : BRec :=
  { colBkt B nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes') with
    ns := (colBkt B nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes')).ns.insert lc (colRe rc null) }

/-- The records of the root, the child and the child's children after the collapse's loop. -/
def colF (B : BRec) (nl lc : Loc) (rn rc : NRec) (l : Loc) : NRec :=
  if l = nl then colRoot rn rc rc.nv.inodes' else if l = lc then colRe rc null else
    colKid B rc.ws nl rc rc.ws.length l

/-- **Closing the heap after the collapse's loop** (`wtxHeap_setBkt_live_acc`'s premises). -/
theorem colBktL_close (B : BRec) (nl lc : Loc) (rn rc : NRec)
    (hrn : B.ns !! nl = some rn) (hrc : B.ns !! lc = some rc) (hlcn : lc ≠ nl)
    (hnn : nl ≠ null) (hlnn : lc ≠ null) (hpn : rn.nv.parent' = null)
    (hchar : ∀ c, c ∈ kidsOf B rc.ws ↔ ∃ rk, B.ns !! c = some rk ∧ rk.nv.parent' = lc)
    (hkn : ∀ c ∈ kidsOf B rc.ws, c ≠ nl ∧ c ≠ lc) :
    (∀ l ∈ [nl, lc] ++ kidsOf B rc.ws,
      (colBktL B nl lc rn rc).ns !! l = some (colF B nl lc rn rc l)) ∧
    (∀ l, l ∉ [nl, lc] ++ kidsOf B rc.ws → (colBktL B nl lc rn rc).ns !! l = B.ns !! l) ∧
    (∀ l ∈ [nl, lc] ++ kidsOf B rc.ws, (colF B nl lc rn rc l).nv.parent' ≠ l) := by
  have hns : ∀ l, (colBktL B nl lc rn rc).ns !! l = if l = lc then some (colRe rc null) else
      (colBkt B nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes')).ns !! l := by
    intro l
    show ((colBkt B nl lc rc.nv.pgid' (colRoot rn rc rc.nv.inodes')).ns.insert lc _) !! l = _
    split
    · rename_i h; subst h; exact GMap.lookup_insert _ _ _
    · exact GMap.lookup_insert_ne _ _ (Ne.symm ‹_›)
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons] at hl
    rcases hl with rfl | rfl | hl
    · rw [hns, if_neg (Ne.symm hlcn), col_ns, if_pos rfl]; unfold colF; rw [if_pos rfl]
    · rw [hns, if_pos rfl]; unfold colF; rw [if_neg hlcn, if_pos rfl]
    · obtain ⟨h1, h2⟩ := hkn l hl
      obtain ⟨rk, hrk, hpk⟩ := (hchar l).1 hl
      rw [hns, if_neg h2, col_ns, if_neg h1, if_neg h2, hrk]
      unfold colF; rw [if_neg h1, if_neg h2, colKid_all _ _ _ _ _ hl, hrk]
      simp only [Option.map_some, hpk, ite_true, Option.getD_some]; rfl
  · simp only [List.cons_append, List.nil_append, List.mem_cons, not_or] at hl
    obtain ⟨h1, h2, h3⟩ := hl
    rw [hns, if_neg h2, col_ns, if_neg h1, if_neg h2]
    cases hy : B.ns !! l with
    | none => rfl
    | some ry =>
      simp only [Option.map_some, Option.some.injEq]
      rw [if_neg (fun hp => h3 ((hchar l).2 ⟨ry, hy, hp⟩))]
  · simp only [List.cons_append, List.nil_append, List.mem_cons] at hl
    rcases hl with rfl | rfl | hl
    · unfold colF; rw [if_pos rfl]; show rn.nv.parent' ≠ _; rw [hpn]; exact Ne.symm hnn
    · unfold colF; rw [if_neg hlcn, if_pos rfl]; exact Ne.symm hlnn
    · obtain ⟨h1, h2⟩ := hkn l hl
      unfold colF; rw [if_neg h1, if_neg h2, colKid_all _ _ _ _ _ hl]; exact Ne.symm h1

end colmat

end bbolt
end EtcdGrove
end Perennial
