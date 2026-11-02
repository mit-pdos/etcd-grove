/-
Facts the proof of `node.rebalance` needs beyond the steps' lemmas: what `b.node` of an entry
of a branch reads (`entry_srcOK`), what `siblingOK` asks of a node (`rbl_siblingOK`), a full
slice (`slice_full`), and the reparenting loops' intermediate states (`reparentP`).
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceCol
public import Spec.go_etcd_io.bbolt.node__nextSibling

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- What `b.node` reads for an entry of a branch node not materialized: its page in the view. -/
theorem entry_srcOK (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (nl : Loc) (r : NRec) (hr : B.ns !! nl = some r)
    (hb : r.nv.isLeaf' = false) (i : Nat) (w : WEntry) (hw : r.ws[i]? = some w) :
    ∃ p pg src, B.nm !! w.pgid = none → nodeSrcOK W B ∅ w.pgid p pg src := by
  by_cases hn : B.nm !! w.pgid = none
  · have hroot : B.ib.root' ≠ W64 0 := by
      intro h0; have := hc.2.2.2.2.2.2.1 h0 nl r hr; rw [hb] at this; cases this
    have hres : resolve B w.pgid = none := by unfold resolve; rw [if_neg hroot]; exact hn
    obtain ⟨pg, -, hok⟩ := nodeSrcOK_page W hwm B ∅ w.pgid hv (fun _ _ => rfl) (hc.2.2.2.2.2.1 hroot) hroot
      hres (posOK_node_child W hwm bl B nl r hc hr hb i w hw)
    exact ⟨_, pg, Src.view, fun _ => hok⟩
  · exact ⟨null, [], Src.view, fun h => absurd h hn⟩

/-- A child of a branch node in the invariant: its record, its parent the node. -/
theorem kid_pos (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (lc : Loc) (rc : NRec) (hlc : lc ≠ null) (hrc : B.ns !! lc = some rc) (y : Loc) (ry : NRec)
    (hy : B.ns !! y = some ry) (hp : ry.nv.parent' = lc) :
    ∃ (k : Nat) (x : WEntry), rc.ws[k]? = some x ∧ B.nm !! x.pgid = some y := by
  have hn := hc.2.2.2.2.2.2.2.1 y ry hy
  obtain ⟨rp, hrp, -, -, w, hw, hwp⟩ := hn.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by rw [hp]; exact hlc)
  rw [hp, hrc] at hrp; cases hrp
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hw
  exact ⟨k, w, hk, by rw [hwp]; exact hn.2.2.2.2.2.2.1⟩

/-- The entries of a leaf have no materialized node (their page id is 0, not a node's). -/
theorem leaf_nokid (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (dfc : Option Loc)
    (HB : rblB W hwm bl B dfc) (hp0 : W.pages !! 0 = none) (hroot0 : B.ib.root' ≠ W64 0)
    (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry) (hl : ry.nv.isLeaf' = true) (w : WEntry)
    (hw : w ∈ ry.ws) : B.nm !! w.pgid = none := by
  obtain ⟨hc, ⟨bnd, hk⟩, -, -⟩ := HB
  have h0 := ((hk.2.2 y ry hy).2.2.2.2 hl w hw).1
  rw [h0]
  cases hn : B.nm !! W64 0 with
  | none => rfl
  | some l0 =>
    obtain ⟨-, r0, hr0, hpg0⟩ := hc.2.2.2.2.1 _ _ hn
    have hwf := (hc.2.2.2.2.2.2.2.1 l0 r0 hr0).2.2.2.2.2.2.2.2.1 hroot0
    rw [hpg0] at hwf
    cases hwf with
    | page _ pg _ hpg _ _ => rw [show uint.nat (W64 0) = 0 from rfl, hp0] at hpg; cases hpg

open Classical in
/-- The node `ry` at `y` after the first `j` entries `ws` of a reparenting loop: its parent `a`
becomes `b` if one of them is its page. -/
def repStep (nm : GMap w64 Loc) (a b : Loc) (ws : List WEntry) (j : Nat) (y : Loc) (ry : NRec) :
    NRec :=
  if ry.nv.parent' = a ∧ ∃ (k : Nat) (x : WEntry), k < j ∧ ws[k]? = some x ∧ nm !! x.pgid = some y then
    { ry with nv := { ry.nv with parent' := b } } else ry

theorem repStep_zero (nm : GMap w64 Loc) (a b : Loc) (ws : List WEntry) (y : Loc) (ry : NRec) :
    repStep nm a b ws 0 y ry = ry := by
  unfold repStep; rw [if_neg]; rintro ⟨-, k, x, hk, -⟩; exact Nat.not_lt_zero _ hk

theorem repStep_succ_ne (nm : GMap w64 Loc) (a b : Loc) (ws : List WEntry) (j : Nat) (x : WEntry)
    (hx : ws[j]? = some x) (y : Loc) (hy : nm !! x.pgid ≠ some y) (ry : NRec) :
    repStep nm a b ws (j + 1) y ry = repStep nm a b ws j y ry := by
  have hiff : (ry.nv.parent' = a ∧ ∃ (k : Nat) (x : WEntry), k < j + 1 ∧ ws[k]? = some x ∧ nm !! x.pgid = some y) ↔
      (ry.nv.parent' = a ∧ ∃ (k : Nat) (x : WEntry), k < j ∧ ws[k]? = some x ∧ nm !! x.pgid = some y) := by
    constructor
    · rintro ⟨hp, k, x', hk, hx', hn⟩
      refine ⟨hp, k, x', ?_, hx', hn⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h
      · subst h; rw [hx] at hx'; cases hx'; exact absurd hn hy
    · rintro ⟨hp, k, x', hk, hx', hn⟩; exact ⟨hp, k, x', by omega, hx', hn⟩
  unfold repStep
  by_cases h : ry.nv.parent' = a ∧ ∃ (k : Nat) (x : WEntry), k < j ∧ ws[k]? = some x ∧ nm !! x.pgid = some y
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

theorem repStep_hit (nm : GMap w64 Loc) (a b : Loc) (ws : List WEntry) (j : Nat) (x : WEntry)
    (hx : ws[j]? = some x) (y : Loc) (hy : nm !! x.pgid = some y) (ry : NRec)
    (hp : ry.nv.parent' = a) :
    repStep nm a b ws (j + 1) y ry = { ry with nv := { ry.nv with parent' := b } } := by
  unfold repStep; rw [if_pos ⟨hp, j, x, Nat.lt_succ_self j, hx, hy⟩]

theorem repStep_set (nm : GMap w64 Loc) (a b : Loc) (ws : List WEntry) (j : Nat) (y : Loc)
    (ry : NRec) :
    ({ repStep nm a b ws j y ry with nv := { (repStep nm a b ws j y ry).nv with parent' := b } } : NRec) =
      { ry with nv := { ry.nv with parent' := b } } := by
  unfold repStep; split <;> rfl

theorem repStep_fresh (nm : GMap w64 Loc) (a b : Loc) (ws : List WEntry) (j : Nat) (x : WEntry)
    (hnd : (ws.map WEntry.pgid).Nodup) (y : Loc)
    (hinj : ∀ p q, nm !! p = some y → nm !! q = some y → p = q)
    (hx : ws[j]? = some x) (hy : nm !! x.pgid = some y) (ry : NRec) :
    repStep nm a b ws j y ry = ry := by
  unfold repStep; rw [if_neg]; rintro ⟨-, k, x', hk, hx', hn⟩
  have he := hinj _ _ hn hy
  have hkl : k < ws.length := (List.getElem?_eq_some_iff.1 hx').1
  have hjl : j < ws.length := (List.getElem?_eq_some_iff.1 hx).1
  have e1 : (ws.map WEntry.pgid)[k]'(by simpa using hkl) =
      (ws.map WEntry.pgid)[j]'(by simpa using hjl) := by
    simp only [List.getElem_map]
    rw [(List.getElem?_eq_some_iff.1 hx').2, (List.getElem?_eq_some_iff.1 hx).2]; exact he
  have := (List.Nodup.getElem_inj hnd).1 e1
  omega

theorem repStep_all (nm : GMap w64 Loc) (a b : Loc) (ws : List WEntry) (y : Loc) (ry : NRec)
    (hall : ry.nv.parent' = a → ∃ (k : Nat) (x : WEntry), ws[k]? = some x ∧ nm !! x.pgid = some y) :
    repStep nm a b ws ws.length y ry =
      if ry.nv.parent' = a then { ry with nv := { ry.nv with parent' := b } } else ry := by
  unfold repStep
  by_cases hp : ry.nv.parent' = a
  · obtain ⟨k, x, hx, hn⟩ := hall hp
    rw [if_pos ⟨hp, k, x, (List.getElem?_eq_some_iff.1 hx).1, hx, hn⟩, if_pos hp]
  · rw [if_neg (fun h => hp h.1), if_neg hp]

/-- After the collapse: the bucket in the invariant, the step from the bucket before the
rebalance (`B`, its root `nl` cleared and its child materialized: `B1`). -/
theorem col_post (W : WView) (hwm : Nat) (bl : Loc) (B B1 : BRec) (nl lc : Loc) (r rn rc : NRec)
    (w0 : WEntry) (sI : GoSlice)
    (HB1 : rblB W hwm bl B1 (some nl))
    (hbv : B1.bv = B.bv) (hib : B1.ib = B.ib) (hbm : B1.bm = B.bm)
    (hun : ∀ y ry', B1.ns !! y = some ry' → ry'.nv.unbalanced' = true →
      ∃ ry, (rblStart B nl r).ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
        ry'.nv.pgid' = ry.nv.pgid')
    (hrn : B1.ns !! nl = some rn) (hbr : rn.nv.isLeaf' = false) (hpn : rn.nv.parent' = null)
    (hws : rn.ws = [w0]) (hlc : B1.nm !! w0.pgid = some lc) (hrc : B1.ns !! lc = some rc) :
    rblB W hwm bl (colBkt B1 nl lc rc.nv.pgid' (colRoot rn rc sI)) none ∧
      rblStep B (colBkt B1 nl lc rc.nv.pgid' (colRoot rn rc sI)) nl ∧
      ∀ k v, entryIn W B1 k v → entryIn W (colBkt B1 nl lc rc.nv.pgid' (colRoot rn rc sI)) k v := by
  obtain ⟨H1, H2, H3⟩ := rbl_col W hwm bl B1 nl rn w0 lc rc sI HB1 hrn hbr hpn hws hlc hrc
  have hst : ∀ y ry, (rblStart B nl r).ns !! y = some ry → ry.nv.unbalanced' = true →
      y ≠ nl ∧ B.ns !! y = some ry := by
    intro y ry hy hu
    change (<[nl := rblClear r]> B.ns) !! y = some ry at hy
    rw [rf_lookup] at hy
    split at hy
    · cases hy; simp [rblClear] at hu
    · rename_i h; exact ⟨h, hy⟩
  refine ⟨H1, ⟨hbv, hib, hbm, fun y ry' hy hu => ?_⟩, H2⟩
  rcases H3 y ry' hy hu with ⟨rfl, hu'⟩ | ⟨-, ry, hry, hu1, hp1⟩
  · obtain ⟨ry, hry, hu0, -⟩ := hun _ rn hrn hu'
    exact absurd rfl (hst _ ry hry hu0).1
  · obtain ⟨ry0, hry0, hu0, hp0⟩ := hun y ry hry hu1
    obtain ⟨hyn, hB⟩ := hst y ry0 hry0 hu0
    exact ⟨hyn, ry0, hB, hu0, hp1.trans hp0⟩

/-- A search for a key of sorted entries finds it. -/
theorem wSearch_eq (ws : List WEntry) (hs : wsSorted ws) (key : List w8) (i : Nat)
    (hi : i < ws.length) (hk : wKey ws i = key) (j : Nat) (h : wSearch ws key j) : j = i := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases Nat.lt_trichotomy j i with hlt | heq | hgt
  · have := hs j i hlt hi
    rw [hk] at this
    exact absurd this (h3 (by omega))
  · exact heq
  · have := h2 i hgt
    rw [hk] at this
    exact absurd this (goStringLt_irrefl_w key)

/-- What `nextSibling`/`prevSibling` ask of a node with a parent in the invariant. -/
theorem rbl_siblingOK (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (dfc : Option Loc)
    (hv : viewOK W) (HB : rblB W hwm bl B dfc) (nl : Loc) (r : NRec) (hr : B.ns !! nl = some r)
    (hpn : r.nv.parent' ≠ null) (hks : r.ksrc ≠ Src.stale) : siblingOK W B ∅ bl nl r := by
  obtain ⟨hc, -, ha, -⟩ := HB
  right
  obtain ⟨rp, hrp, hbr, -, -⟩ := (hc.2.2.2.2.2.2.2.1 nl r hr).2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
  have hpnl : r.nv.parent' ≠ nl := by
    intro he; obtain ⟨ht, hh⟩ := ha; have := hh nl r hr hpn; rw [he] at this; omega
  have hnp := hc.2.2.2.2.2.2.2.1 _ rp hrp
  refine ⟨rp, hrp, hpnl, hbr, hnp.1, hnp.2.2.1, hnp.2.2.2.2.1, hks, fun w hw =>
    ⟨fun l hl => (hc.2.2.2.2.1 _ _ hl).1, fun hn => ?_⟩⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hw
  obtain ⟨p, pg, src, h⟩ := entry_srcOK W hwm bl B hv hc _ rp hrp hbr i w hi
  exact ⟨p, pg, src, h hn⟩

/-- The unbalanced nodes at the start: not the node, those of the bucket. -/
theorem rblStart_unbal (B : BRec) (nl : Loc) (r : NRec) (y : Loc) (ry : NRec)
    (hy : (rblStart B nl r).ns !! y = some ry) (hu : ry.nv.unbalanced' = true) :
    y ≠ nl ∧ B.ns !! y = some ry := by
  change (<[nl := rblClear r]> B.ns) !! y = some ry at hy
  rw [rf_lookup] at hy
  split at hy
  · cases hy; simp [rblClear] at hu
  · rename_i h; exact ⟨h, hy⟩

/-- Before the parent's rebalance, after a merge (`B2`) following the materialization of a
sibling (`B1`). -/
theorem mg_pre (B B1 B2 : BRec) (nl pl lr : Loc) (r : NRec)
    (hbv : B1.bv = B.bv) (hib : B1.ib = B.ib) (hbm : B1.bm = B.bm)
    (hun1 : ∀ y ry', B1.ns !! y = some ry' → ry'.nv.unbalanced' = true →
      ∃ ry, (rblStart B nl r).ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
        ry'.nv.pgid' = ry.nv.pgid')
    (hbv2 : B2.bv = B1.bv) (hib2 : B2.ib = B1.ib) (hbm2 : B2.bm = B1.bm)
    (hun2 : ∀ y ry', B2.ns !! y = some ry' → ry'.nv.unbalanced' = true →
      y = pl ∨ (y ≠ lr ∧ ∃ ry, B1.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
        ry'.nv.pgid' = ry.nv.pgid')) :
    rblPre B B2 nl pl := by
  refine ⟨hbv2.trans hbv, hib2.trans hib, hbm2.trans hbm, fun y ry' hy hu => ?_⟩
  rcases hun2 y ry' hy hu with h | ⟨-, ry, hry, hu1, hp1⟩
  · exact Or.inl h
  · obtain ⟨ry0, hry0, hu0, hp0⟩ := hun1 y ry hry hu1
    obtain ⟨hyn, hB⟩ := rblStart_unbal B nl r y ry0 hry0 hu0
    exact Or.inr ⟨hyn, ry0, hB, hu0, hp1.trans hp0⟩

end pure


section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

open Iris.ProofMode in
/-- A step of a reparenting loop whose entry has no node: nothing changes. -/
theorem rep_none (W : WView) (D : GMap Loc NRec) (nm : GMap w64 Loc) (a b : Loc) (ws : List WEntry)
    (j : Nat) (x : WEntry) (hx : ws[j]? = some x) (hn : nm !! x.pgid = none) :
    ([∗map] y ↦ ry ∈ D, nodeOwn (GF := GF) W y (repStep nm a b ws j y ry)) ⊢
      [∗map] y ↦ ry ∈ D, nodeOwn W y (repStep nm a b ws (j + 1) y ry) := by
  refine BigSepM.bigSepM_mono_of_forall fun {y ry} => ?_
  rw [repStep_succ_ne nm a b ws j x hx y (by rw [hn]; nofun) ry]

open Iris.ProofMode in
/-- A step of a reparenting loop whose entry has the node `c`: `c` taken out, put back changed. -/
theorem rep_hit (W : WView) (D : GMap Loc NRec) (nm : GMap w64 Loc) (a b : Loc) (ws : List WEntry)
    (j : Nat) (x : WEntry) (hx : ws[j]? = some x) (c : Loc) (hc : nm !! x.pgid = some c) (rc : NRec)
    (hD : D !! c = some rc) :
    ([∗map] y ↦ ry ∈ D, nodeOwn (GF := GF) W y (repStep nm a b ws j y ry)) ⊢
      nodeOwn W c (repStep nm a b ws j c rc) ∗
      (nodeOwn W c (repStep nm a b ws (j + 1) c rc) -∗
        [∗map] y ↦ ry ∈ D, nodeOwn W y (repStep nm a b ws (j + 1) y ry)) := by
  iintro H
  icases (BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun y ry => nodeOwn (GF := GF) W y (repStep nm a b ws j y ry))
    (show Std.get? D c = some rc from hD)).1 $$ H with ⟨Hc, H⟩
  iframe Hc
  iintro Hc
  iapply (BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun y ry => nodeOwn (GF := GF) W y (repStep nm a b ws (j + 1) y ry))
    (show Std.get? D c = some rc from hD)).2
  iframe Hc
  iapply (BigSepM.bigSepM_mono (M := GMap Loc)
    (Φ := fun y ry => nodeOwn (GF := GF) W y (repStep nm a b ws j y ry))
    (Ψ := fun y ry => nodeOwn (GF := GF) W y (repStep nm a b ws (j + 1) y ry)) ?_) $$ H
  intro y ry hy
  have hyc : y ≠ c := by
    rintro rfl; rw [Iris.Std.get?_delete_eq rfl] at hy; cases hy
  rw [repStep_succ_ne nm a b ws j x hx y
    (by rw [hc]; intro h; exact hyc (Option.some.inj h).symm) ry]

open Iris.ProofMode in
/-- The nodes after the collapse's reparenting loop and the root's new record: the bucket's
nodes after the collapse. -/
theorem col_own (W : WView) (B : BRec) (nl lc : Loc) (pgid : w64) (rn' : NRec) (ws : List WEntry)
    (hall : ∀ y ry, B.ns !! y = some ry → y ≠ nl → y ≠ lc → ry.nv.parent' = lc →
      ∃ (k : Nat) (x : WEntry), ws[k]? = some x ∧ B.nm !! x.pgid = some y) :
    ([∗map] y ↦ ry ∈ Std.delete (Std.delete B.ns nl) lc,
        nodeOwn (GF := GF) W y (repStep B.nm lc nl ws ws.length y ry)) ∗ nodeOwn W nl rn' ⊢
      [∗map] y ↦ ry ∈ (colBkt B nl lc pgid rn').ns, nodeOwn W y ry := by
  let f : NRec → NRec := fun x =>
    if x.nv.parent' = lc then { x with nv := { x.nv with parent' := nl } } else x
  let D0 : GMap Loc NRec := GMap.delete lc (GMap.delete nl B.ns)
  have hD0 : ∀ y, D0 !! y = if y = nl ∨ y = lc then none else B.ns !! y := by
    intro y
    show (GMap.delete lc (GMap.delete nl B.ns)) !! y = _
    by_cases h1 : y = lc
    · subst h1; rw [GMap.lookup_delete, if_pos (Or.inr rfl)]
    rw [GMap.lookup_delete_ne _ (Ne.symm h1)]
    by_cases h2 : y = nl
    · subst h2; rw [GMap.lookup_delete, if_pos (Or.inl rfl)]
    rw [GMap.lookup_delete_ne _ (Ne.symm h2), if_neg (by rintro (h | h) <;> contradiction)]
  have he : (colBkt B nl lc pgid rn').ns = <[nl := rn']> (GMap.fmap f D0) := by
    apply GMap.ext; intro y
    rw [col_ns, rf_lookup, GMap.lookup_fmap, hD0]
    by_cases h1 : y = nl
    · rw [if_pos h1, if_pos h1]
    rw [if_neg h1, if_neg h1]
    by_cases h2 : y = lc
    · rw [if_pos h2, if_pos (Or.inr h2)]; rfl
    rw [if_neg h2, if_neg (by rintro (h | h) <;> contradiction)]
  have hfm : (GMap.fmap f D0 : GMap Loc NRec) = Iris.Std.PartialMap.map f D0 := by
    apply GMap.ext; intro y
    show (GMap.fmap f D0) !! y = Std.get? (Iris.Std.PartialMap.map f D0) y
    rw [GMap.lookup_fmap, Iris.Std.LawfulPartialMap.get?_map]; rfl
  have hD0' : (Std.delete (Std.delete B.ns nl) lc : GMap Loc NRec) = D0 := rfl
  rw [he, hD0']
  iintro ⟨H, Hn⟩
  iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun y x => nodeOwn (GF := GF) W y x)
    (show Std.get? (GMap.fmap f D0) nl = none by
      show (GMap.fmap f D0) !! nl = none
      rw [GMap.lookup_fmap, hD0, if_pos (Or.inl rfl)]; rfl)).2
  iframe Hn
  rw [hfm, BigSepM.bigSepM_map]
  iapply (BigSepM.bigSepM_mono (M := GMap Loc)
    (Φ := fun y ry => nodeOwn (GF := GF) W y (repStep B.nm lc nl ws ws.length y ry))
    (Ψ := fun y x => nodeOwn (GF := GF) W y (f x)) ?_) $$ H
  intro y ry hy
  change D0 !! y = some ry at hy
  rw [hD0] at hy
  split at hy
  · cases hy
  rename_i hyn
  rw [repStep_all B.nm lc nl ws y ry
    (fun hp => hall y ry hy (fun h => hyn (Or.inl h)) (fun h => hyn (Or.inr h)) hp)]

open Iris.ProofMode in
/-- The nodes after the merge's reparenting loop, the left node's and the parent's new records:
the bucket's nodes after the merge. -/
theorem mg_own (W : WView) (B : BRec) (pl ll lr : Loc) (pgid : w64) (rp' rl' : NRec)
    (ws : List WEntry) (hlp : ll ≠ pl)
    (hall : ∀ y ry, B.ns !! y = some ry → y ≠ pl → y ≠ ll → y ≠ lr → ry.nv.parent' = lr →
      ∃ (k : Nat) (x : WEntry), ws[k]? = some x ∧ B.nm !! x.pgid = some y) :
    ([∗map] y ↦ ry ∈ Std.delete (Std.delete (Std.delete B.ns pl) ll) lr,
        nodeOwn (GF := GF) W y (repStep B.nm lr ll ws ws.length y ry)) ∗ nodeOwn W ll rl' ∗
      nodeOwn W pl rp' ⊢
      [∗map] y ↦ ry ∈ (mgBkt B pl ll lr pgid rp' rl').ns, nodeOwn W y ry := by
  let f : NRec → NRec := fun x =>
    if x.nv.parent' = lr then { x with nv := { x.nv with parent' := ll } } else x
  let D0 : GMap Loc NRec := GMap.delete lr (GMap.delete ll (GMap.delete pl B.ns))
  have hD0 : ∀ y, D0 !! y = if y = pl ∨ y = ll ∨ y = lr then none else B.ns !! y := by
    intro y
    show (GMap.delete lr (GMap.delete ll (GMap.delete pl B.ns))) !! y = _
    by_cases h1 : y = lr
    · subst h1; rw [GMap.lookup_delete, if_pos (Or.inr (Or.inr rfl))]
    rw [GMap.lookup_delete_ne _ (Ne.symm h1)]
    by_cases h2 : y = ll
    · subst h2; rw [GMap.lookup_delete, if_pos (Or.inr (Or.inl rfl))]
    rw [GMap.lookup_delete_ne _ (Ne.symm h2)]
    by_cases h3 : y = pl
    · subst h3; rw [GMap.lookup_delete, if_pos (Or.inl rfl)]
    rw [GMap.lookup_delete_ne _ (Ne.symm h3), if_neg (by rintro (h | h | h) <;> contradiction)]
  have he : (mgBkt B pl ll lr pgid rp' rl').ns = <[pl := rp']> (<[ll := rl']> (GMap.fmap f D0)) := by
    apply GMap.ext; intro y
    rw [mg_ns, rf_lookup, rf_lookup, GMap.lookup_fmap, hD0]
    by_cases h1 : y = pl
    · rw [if_pos h1, if_pos h1]
    rw [if_neg h1, if_neg h1]
    by_cases h2 : y = ll
    · rw [if_pos h2, if_pos h2]
    rw [if_neg h2, if_neg h2]
    by_cases h3 : y = lr
    · rw [if_pos h3, if_pos (Or.inr (Or.inr h3))]; rfl
    rw [if_neg h3, if_neg (by rintro (h | h | h) <;> contradiction)]
  have hfm : (GMap.fmap f D0 : GMap Loc NRec) = Iris.Std.PartialMap.map f D0 := by
    apply GMap.ext; intro y
    show (GMap.fmap f D0) !! y = Std.get? (Iris.Std.PartialMap.map f D0) y
    rw [GMap.lookup_fmap, Iris.Std.LawfulPartialMap.get?_map]; rfl
  have hD0' : (Std.delete (Std.delete (Std.delete B.ns pl) ll) lr : GMap Loc NRec) = D0 := rfl
  rw [he, hD0']
  iintro ⟨H, Hl, Hp⟩
  iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun y x => nodeOwn (GF := GF) W y x)
    (show Std.get? (<[ll := rl']> (GMap.fmap f D0)) pl = none by
      show (<[ll := rl']> (GMap.fmap f D0)) !! pl = none
      rw [rf_lookup, if_neg (Ne.symm hlp), GMap.lookup_fmap, hD0, if_pos (Or.inl rfl)]; rfl)).2
  iframe Hp
  iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun y x => nodeOwn (GF := GF) W y x)
    (show Std.get? (GMap.fmap f D0) ll = none by
      show (GMap.fmap f D0) !! ll = none
      rw [GMap.lookup_fmap, hD0, if_pos (Or.inr (Or.inl rfl))]; rfl)).2
  iframe Hl
  rw [hfm, BigSepM.bigSepM_map]
  iapply (BigSepM.bigSepM_mono (M := GMap Loc)
    (Φ := fun y ry => nodeOwn (GF := GF) W y (repStep B.nm lr ll ws ws.length y ry))
    (Ψ := fun y x => nodeOwn (GF := GF) W y (f x)) ?_) $$ H
  intro y ry hy
  change D0 !! y = some ry at hy
  rw [hD0] at hy
  split at hy
  · cases hy
  rename_i hyn
  rw [repStep_all B.nm lr ll ws y ry (fun hp => hall y ry hy (fun h => hyn (Or.inl h))
    (fun h => hyn (Or.inr (Or.inl h))) (fun h => hyn (Or.inr (Or.inr h))) hp)]

end own



end bbolt
end EtcdGrove
end Perennial
