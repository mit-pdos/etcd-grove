/-
At `Commit`: the clean write transaction with its shape (`txShape`) over a view whose pages have
heights (`pageHts`, from `treeStrict`) is ready for `rebalance` (`rblReady`,
`RebalanceDefs.lean`): `rblReady_of_shape`.

Everything but the exact keys comes from the nodes' pages (`bktPg`, `NodePages.lean`):
- heights (`rblHt`): a leaf 0, a branch its page's height (`pht`), which is one more than its
  children's pages', hence than its materialized children (a leaf child was read from a leaf
  page, of height 0; a branch child has its page's height);
- the parent pointers have no cycle (`rblAcyc`): a node is an entry of its parent's (`nodeClean`),
  so the parent is one higher;
- a leaf's entries have `pgid` 0 (`leafPg0`);
- a branch's lower bound is its first key (`brFirst`): the lower bound is the parent's entry's
  key (the node's key, its first entry's) or, under the parent's first entry, the parent's lower
  bound, its first key by induction up the parent chain (on the heights: the nodes are finitely
  many, so their heights are bounded).
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceDefs
public import Proof.go_etcd_io.bbolt.NodePages

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace RblReady

section pure
variable [ext : FfiSyntax]

theorem le_sum_of_mem (f : Loc → Nat) (L : List Loc) (k : Loc) (h : k ∈ L) :
    f k ≤ (L.map f).sum := by
  induction L with
  | nil => cases h
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- A function is bounded on a finite map's keys. -/
theorem bound (m : GMap Loc NRec) (f : Loc → Nat) : ∃ N, ∀ k, (m !! k).isSome → f k ≤ N := by
  obtain ⟨L, hL⟩ := m.finite
  exact ⟨(L.map f).sum, fun k hk => le_sum_of_mem f L k (hL k hk)⟩

/-- The heights of the nodes: a leaf 0, a branch its page's. -/
def ht (B : BRec) (pht : Nat → Nat) (l : Loc) : Nat :=
  match B.ns !! l with
  | some r => if r.nv.isLeaf' = true then 0 else pht (uint.nat r.nv.pgid')
  | none => 0

theorem ht_of (B : BRec) (pht : Nat → Nat) (l : Loc) (r : NRec) (h : B.ns !! l = some r) :
    ht B pht l = if r.nv.isLeaf' = true then 0 else pht (uint.nat r.nv.pgid') := by
  unfold ht; rw [h]

section bkt
variable (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
  (hp : bktPg W B) (pht : Nat → Nat) (hph : pageHts W.pages pht)
include hc hp hph

/-- A branch is one higher than its children, nodes or pages. -/
theorem ht_branch (l : Loc) (r : NRec) (hl : B.ns !! l = some r) (hb : r.nv.isLeaf' = false)
    (w : WEntry) (hw : w ∈ r.ws) :
    (∀ l', B.nm !! w.pgid = some l' → ht B pht l' + 1 = ht B pht l) ∧
    (B.nm !! w.pgid = none → pht (uint.nat w.pgid) + 1 = ht B pht l) := by
  obtain ⟨-, -, -, -, hc5, -, hc7, -, -, -⟩ := hc
  obtain ⟨-, pg, hpg, hfl, hlen, hpid⟩ := (hp l r hl).2 hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hw
  have hlt : i < pageCount pg := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
  have hwp := hpid i w hi
  have hu : uint.nat w.pgid = branchPgid pg i := by
    rw [hwp]; exact uint_nat_W64_w _ (branchPgid_lt pg i)
  have hh := (hph _ pg hpg).2 hfl i hlt
  have hl' : ht B pht l = pht (uint.nat r.nv.pgid') := by rw [ht_of B pht l r hl, hb]; rfl
  refine ⟨fun l' hl'' => ?_, fun _ => by rw [hl', hu]; exact hh⟩
  obtain ⟨-, r', hr', hpg'⟩ := hc5 _ _ hl''
  have hr0 : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc7 h0 l r hl; rw [hb] at this; cases this
  rw [hl', ht_of B pht l' r' hr', ← hh, ← hu]
  cases hlf : r'.nv.isLeaf'
  · rw [if_neg (by simp), hpg']
  · rw [if_pos rfl]
    obtain ⟨q, hq, hqf⟩ := ((hp l' r' hr').1 hlf).2 hr0
    rw [hpg'] at hq
    rw [(hph _ q hq).1 hqf]

/-- The heights (`rblHt`). -/
theorem rblHt_of : rblHt W B :=
  ⟨ht B pht, pht, hph, fun l r hl =>
    ⟨fun hlf => by rw [ht_of B pht l r hl, if_pos hlf],
     fun hb w hw => ht_branch W hwm bl B hc hp pht hph l r hl hb w hw⟩⟩

/-- A node's parent is one higher. -/
theorem ht_parent (l : Loc) (r : NRec) (hl : B.ns !! l = some r) (hpn : r.nv.parent' ≠ null) :
    ∃ rp, B.ns !! r.nv.parent' = some rp ∧ rp.nv.isLeaf' = false ∧
      ht B pht l + 1 = ht B pht r.nv.parent' := by
  obtain ⟨-, -, -, -, -, -, h7, -, -, -, -, -, -, h14, -⟩ := hc.2.2.2.2.2.2.2.1 l r hl
  obtain ⟨rp, hrp, hb, -, w, hw, hwp⟩ := h14 hpn
  refine ⟨rp, hrp, hb, ?_⟩
  exact (ht_branch W hwm bl B hc hp pht hph _ rp hrp hb w hw).1 l (by rw [hwp]; exact h7)

/-- No cycle of parent pointers (`rblAcyc`). -/
theorem rblAcyc_of : rblAcyc B :=
  ⟨ht B pht, fun l r hl hpn => by
    obtain ⟨-, -, -, h⟩ := ht_parent W hwm bl B hc hp pht hph l r hl hpn; omega⟩

/-- A branch's lower bound is its first key (`brFirst`). -/
theorem brFirst_of (bnd : Loc → Option (List w8) × Option (List w8)) (hk : bktKeysB W B bnd) :
    brFirst B bnd := by
  obtain ⟨N, hN⟩ := bound B.ns (ht B pht)
  have key : ∀ d l r, B.ns !! l = some r → N - ht B pht l ≤ d → r.nv.isLeaf' = false →
      ∀ x, (bnd l).1 = some x → wKey r.ws 0 = x := by
    intro d
    induction d with
    | zero =>
      intro l r hl hd hb x hx
      obtain ⟨-, c2, -⟩ := hk.2.2 l r hl
      by_cases hpn : r.nv.parent' = null
      · rw [c2 hpn] at hx; cases hx
      · obtain ⟨rp, hrp, -, h⟩ := ht_parent W hwm bl B hc hp pht hph l r hl hpn
        have := hN _ (by rw [hrp]; rfl); omega
    | succ d ih =>
      intro l r hl hd hb x hx
      obtain ⟨-, c2, c3, -⟩ := hk.2.2 l r hl
      by_cases hpn : r.nv.parent' = null
      · rw [c2 hpn] at hx; cases hx
      obtain ⟨-, rp, i, w, hrp, hw, -, hwk, hbe⟩ := c3 hpn
      have hrk : r.key = wKey r.ws 0 := ((hp l r hl).2 hb).1
      have hwi : wKey rp.ws i = w.key := by simp [wKey, hw]
      rw [hbe] at hx
      unfold entryBnd childLo at hx
      simp only at hx
      split at hx
      · rename_i hi0
        subst hi0
        obtain ⟨rp', hrp', hbp, h⟩ := ht_parent W hwm bl B hc hp pht hph l r hl hpn
        rw [hrp] at hrp'; cases hrp'
        have hNp := hN _ (by rw [hrp]; rfl)
        have := ih _ rp hrp (by omega) hbp x hx
        rw [← hrk, ← hwk, ← hwi, this]
      · cases hx
        rw [← hrk, ← hwk, ← hwi]
  intro l r hl hb x hx
  exact key _ l r hl (Nat.le_refl _) hb x hx

end bkt

/-- The leaves' entries have no child page (`leafPg0`). -/
theorem leafPg0_of (W : WView) (B : BRec) (hp : bktPg W B) : leafPg0 B :=
  fun l r hl hlf => ((hp l r hl).1 hlf).1

end pure

end RblReady

section pure
variable [ext : FfiSyntax]

/-- At `Commit`: the clean transaction's buckets with their keys and their nodes' pages, over a
view whose pages have heights, are ready for `rebalance`. -/
theorem rblReady_of (W : WView) (txl rl : Loc) (T : WTx) (hc : txClean W txl rl T)
    (hpht : ∃ pht, pageHts W.pages pht)
    (hk : ∀ bl B, T.bs !! bl = some B → bktKeys W B ∧ bktPg W B) : rblReady W T := by
  obtain ⟨pht, hph⟩ := hpht
  intro bl B hB
  have hcl := (hc.2.2.2.2.2.2.2 bl B hB).2.1
  obtain ⟨⟨bnd, hkb⟩, hp⟩ := hk bl B hB
  exact ⟨⟨bnd, hkb, RblReady.brFirst_of W _ bl B hcl hp pht hph bnd hkb⟩,
    RblReady.leafPg0_of W B hp, RblReady.rblAcyc_of W _ bl B hcl hp pht hph,
    RblReady.rblHt_of W _ bl B hcl hp pht hph⟩

end pure


section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

open Iris.ProofMode in
/-- At `Commit`: the write transaction with its shape, over a view whose pages have heights
(`treeStrict`'s last part), is ready for `rebalance`. -/
theorem rblReady_of_shape (γ : GName) (W : WView) (txl : Loc) (T : WTx)
    (hpht : ∃ pht, pageHts W.pages pht) :
    ownWriteTx (GF := GF) W txl T ∗ txShape γ W T ⊢
      ⌜rblReady W T⌝ ∗ ownWriteTx W txl T ∗ txShape γ W T := by
  unfold ownWriteTx txShape
  iintro ⟨⟨Hg, Hv, %Hok⟩, %M, Ha, %Hd, Hbs, %Hf, %Hp⟩
  isplitr
  · ipureintro
    exact rblReady_of W txl _ T Hok.2 hpht (fun bl B hB => ⟨(Hf bl B hB).1, Hp bl B hB⟩)
  isplitl [Hg Hv]
  · iframe; ipureintro; exact Hok
  · iexists M; iframe; ipureintro; exact ⟨Hd, Hf, Hp⟩

end own

end bbolt
end EtcdGrove
end Perennial
