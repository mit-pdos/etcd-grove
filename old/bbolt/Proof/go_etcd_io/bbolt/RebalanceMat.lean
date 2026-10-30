/-
A page position materialized during rebalance (`b.node` of a sibling, or of a root's only child):
the bucket stays in the rebalance's invariant (`rblB_addChild`), the new node's bounds its
entry's (it is a branch's first key there: `brFirst`); its tokens and the nested buckets'
entries are `ShapeMat.lean`'s (`bktToks_addChild`, `entryIn_addChild`).
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceStart
public import Proof.go_etcd_io.bbolt.ShapeMat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- A node's keys during rebalance in a bucket that grew by a node (see the hypotheses). -/
theorem rblNodeKeys_frame (W : WView) (B B' : BRec) (bnd bnd' : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) (y : Loc) (ry ry' : NRec) (h : rblNodeKeys W B bnd dfc y ry)
    (hb : bnd' y = bnd y)
    (hbp : ry.nv.parent' ≠ null → bnd' ry.nv.parent' = bnd ry.nv.parent')
    (hws : ry'.ws = ry.ws) (hpar : ry'.nv.parent' = ry.nv.parent') (hleaf : ry'.nv.isLeaf' = ry.nv.isLeaf')
    (hkey' : ry'.nv.key' = ry.nv.key') (hkey : ry'.key = ry.key) (hpgid : ry'.nv.pgid' = ry.nv.pgid')
    (hunb : ry'.nv.unbalanced' = ry.nv.unbalanced') (hbm : B'.bm = B.bm)
    (hns : ∀ z rz, B.ns !! z = some rz → ∃ rz', B'.ns !! z = some rz' ∧ rz'.ws = rz.ws ∧
      rz'.nv.isLeaf' = rz.nv.isLeaf')
    (hnmB : ∀ k l', B'.nm !! k = some l' → B.nm !! k = some l' ∨ (B.nm !! k = none ∧
      ∃ r', B'.ns !! l' = some r' ∧ ∀ pg, W.pages !! uint.nat k = some pg →
        r'.nv.isLeaf' = decide (pageFlags pg = leafPageFlag)))
    (hnmN : ∀ k, B'.nm !! k = none → B.nm !! k = none) : rblNodeKeys W B' bnd' dfc y ry' := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  refine ⟨by rw [hws, hb]; exact c1, ?_, ?_, by rw [hleaf, hunb, hpar, hws]; exact c4, by
      rw [hleaf, hws]; intro hl w hw
      refine ⟨(c5 hl w hw).1, fun hbk h0 hno => (c5 hl w hw).2 hbk h0 ?_⟩
      unfold opened at hno ⊢; rwa [hbm] at hno⟩
  · intro hp
    rw [hpar] at hp
    obtain ⟨hk', rp0, i0, w0, hrp0, hw0, hpg0, hkey0, hbnd0⟩ := c2 hp
    obtain ⟨rp0', h1, h2, -⟩ := hns _ _ hrp0
    refine ⟨by rw [hkey']; exact hk', rp0', i0, w0, by rw [hpar]; exact h1, by rw [h2]; exact hw0,
      by rw [hpgid]; exact hpg0, by rw [hkey]; exact hkey0, ?_⟩
    rw [hb, hpar, hbp hp, h2]; exact hbnd0
  · intro hlf
    rw [hleaf] at hlf
    obtain ⟨h2, hfst, kind, hkd⟩ := c3 hlf
    refine ⟨by rw [hws]; exact h2, by rw [hb, hws]; exact hfst, kind, fun j w' hj => ?_⟩
    rw [hws] at hj
    obtain ⟨ha, hbb⟩ := hkd j w' hj
    refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
    · rcases hnmB _ _ hl' with ho | ⟨hn0, r', hr', hlf'⟩
      · obtain ⟨r'', h1, h2⟩ := ha l' ho
        obtain ⟨r3, h3, -, h4⟩ := hns _ _ h1
        exact ⟨r3, h3, h4.trans h2⟩
      · obtain ⟨pg0, hpg0, -, hk0, -⟩ := hbb hn0
        exact ⟨r', hr', by rw [hlf' pg0 hpg0]; exact hk0⟩
    · obtain ⟨pg0, a1, a2, a3, a4, a5⟩ := hbb (hnmN _ hn)
      exact ⟨pg0, a1, a2, a3, a4, by rw [hb, hws]; exact a5⟩

theorem pageWs_pgid0 (pg : List w8) (src : Src) (hl : pageFlags pg = leafPageFlag) :
    ∀ w ∈ pageWs pg src, w.pgid = W64 0 := by
  intro w hw
  obtain ⟨j, -, rfl⟩ := pageWs_mem pg src w hw
  unfold pageW; rw [if_pos hl]

section child
variable (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (nl : Loc) (rp : NRec) (i : Nat) (w : WEntry)
    (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false) (hw : rp.ws[i]? = some w)
    (hnone : B.nm !! w.pgid = none) (l : Loc) (hfresh : B.ns !! l = none)
    (hnl : nl ≠ null) (pg : List w8) (hpg : W.pages !! uint.nat w.pgid = some pg) (p : Loc)
    (s cs' : GoSlice) (src' : Src)
include hv hc hrp hbr hw hnone hpg hfresh hnl

/-- Materializing the page position `w.pgid` (entry `i` of the branch node `nl`) keeps the
rebalance's keys, the new node's bounds its entry's. -/
theorem rblKeys_addChild (hrd : pageReadable pg) (bnd : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) (hk : rblKeysB W B bnd dfc) :
    rblKeysB W (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs')
      (fun x => if x = l then entryBnd (bnd nl) rp.ws i else bnd x) dfc := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := hc
  obtain ⟨hk1, hk2, hk3⟩ := hk
  have hlnl : l ≠ nl := by intro h; rw [h, hrp] at hfresh; cases hfresh
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc3 h0).1; rw [this] at hrp; cases hrp
  have hbv' : (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').bv = B.bv := by
    simp [nodeAdded, hnl]
  have hns' := nodeAdded_ns B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp
  have hnsB := ns_addChild B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp hfresh
  have hnm' := nm_addChild W hwm bl B hv ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩
    nl rp i w hrp hbr hw hnone l pg hpg p s cs' src'
  have hfree := free_addChild W hwm bl B hv ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩
    nl rp i w hrp hbr hw hnone l pg hpg p s cs' src'
  obtain ⟨-, -, hrpk3, -, -⟩ := hk3 nl rp hrp
  obtain ⟨-, hrpfst, kind, hkd⟩ := hrpk3 hbr
  obtain ⟨pg', hpg', hcnt, -, hkey0, htk⟩ := (hkd i w hw).2 hnone
  rw [hpg] at hpg'; cases hpg'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrp12, -⟩ := hc8 nl rp hrp
  obtain ⟨-, -, hkids⟩ := hrp12 hbr
  obtain ⟨-, -, hcwf⟩ := hkids w (List.mem_of_getElem? hw)
  obtain ⟨-, hpid, -, -⟩ := treeWF_page _ _ _ pg (hcwf hnone) hpg
  have hold : ∀ x, (B.ns !! x).isSome → x ≠ l := by
    intro x hx he; rw [he, hfresh] at hx; cases hx
  have hpar : ∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ null → (B.ns !! ry.nv.parent').isSome := by
    intro y ry hy hp
    obtain ⟨rq, hrq, -⟩ := (hc8 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
    rw [hrq]; rfl
  have hframe : ∀ y ry ry', B.ns !! y = some ry → ry'.ws = ry.ws →
      ry'.nv.parent' = ry.nv.parent' → ry'.nv.isLeaf' = ry.nv.isLeaf' → ry'.nv.key' = ry.nv.key' →
      ry'.key = ry.key → ry'.nv.pgid' = ry.nv.pgid' → ry'.nv.unbalanced' = ry.nv.unbalanced' →
      rblNodeKeys W (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs')
        (fun x => if x = l then entryBnd (bnd nl) rp.ws i else bnd x) dfc y ry' := by
    intro y ry ry' hy h1 h2 h3 h4 h5 h6 h7
    refine rblNodeKeys_frame W B _ bnd _ dfc y ry ry' (hk3 y ry hy)
      (by rw [if_neg (hold y (by rw [hy]; rfl))])
      (fun hp => by rw [if_neg (hold _ (hpar y ry hy hp))]) h1 h2 h3 h4 h5 h6 h7 rfl
      (fun z rz hz => by
        obtain ⟨rz', a, b, c, -⟩ := hnsB z rz hz; exact ⟨rz', a, b, c⟩) ?_ ?_
    · intro k l' hl'
      rw [hnm'] at hl'
      split at hl'
      · rename_i hkw
        cases hl'
        subst hkw
        refine Or.inr ⟨hnone, _, by rw [hns', if_pos rfl], fun pg0 h0 => ?_⟩
        rw [hpg] at h0; cases h0; rfl
      · exact Or.inl hl'
    · intro k hk0
      rw [hnm'] at hk0
      split at hk0
      · cases hk0
      · exact hk0
  refine ⟨fun h => by rw [hbv'] at h; exact hk1 h, ?_, ?_⟩
  · intro r0 h0
    rw [hbv'] at h0
    rw [hns'] at h0
    have hrs := hc4 hrn
    obtain ⟨-, rr, hrr, -⟩ := hc5 _ _ hrs
    rw [if_neg (hold _ (by rw [hrr]; rfl))] at h0
    split at h0
    · rename_i he
      cases h0
      rw [he] at hrr; rw [hrp] at hrr; cases hrr
      exact hk2 rp (he ▸ hrp)
    · exact hk2 r0 h0
  · intro y ry hy
    rw [hns'] at hy
    split at hy
    · rename_i hyl
      cases hy
      subst hyl
      obtain ⟨n1, n4, n6⟩ := nodeKeys_page W (nodeAdded B w.pgid nl y (readNRec bl nl p pg s src') cs')
        (fun x => if x = y then entryBnd (bnd nl) rp.ws i else bnd x) y
        (readNRec bl nl p pg s src') (uint.nat w.pgid) pg src' (entryBnd (bnd nl) rp.ws i) hpg htk rfl rfl
        (by simp) hfree
      refine ⟨n1, fun _ => ⟨?_, ({ rp with nv := { rp.nv with children' := cs' }, cs := rp.cs ++ [y] } : NRec),
        i, w, ?_, hw, ?_, ?_, ?_⟩, fun hlf => ?_,
        fun _ _ _ _ => by show 0 < (pageWs pg src').length; rw [pageWs_length]; exact hcnt,
        fun hlf w' hw' => ⟨?_, fun hbk h0 _ => n6 hlf w' hw' hbk h0⟩⟩
      · show (if pageCount pg = 0 then slice.nil else (inodeOf p pg 0).key') ≠ slice.nil
        rw [if_neg (by omega)]; exact inodeOf_key_ne_nil p pg hrd hcnt
      · show (nodeAdded B w.pgid nl y (readNRec bl nl p pg s src') cs').ns !! nl = _
        rw [hns', if_neg (Ne.symm hlnl), if_pos rfl]
      · show w.pgid = W64 (pageId pg : Int)
        rw [hpid]; unfold uint.nat; word
      · show w.key = wKey (pageWs pg src') 0
        rw [wKey_pageWs_i _ _ 0 hcnt, pageW_key_pageKey]; exact hkey0.symm
      · show bndIn (if y = y then entryBnd (bnd nl) rp.ws i else bnd y)
          (entryBnd (if nl = y then entryBnd (bnd nl) rp.ws i else bnd nl) rp.ws i)
        rw [if_pos rfl, if_neg (Ne.symm hlnl)]; exact bndIn_refl _
      · obtain ⟨h2, hk⟩ := n4 hlf
        refine ⟨fun _ => h2, ?_, hk⟩
        intro x hx
        simp only [if_pos rfl] at hx
        show wKey (pageWs pg src') 0 = x
        rw [wKey_pageWs_i _ _ 0 hcnt, pageW_key_pageKey, hkey0]
        have hwk : wKey rp.ws i = w.key := by unfold wKey; rw [hw]; rfl
        unfold entryBnd childLo at hx
        by_cases hi0 : i = 0
        · rw [if_pos hi0] at hx; rw [hi0] at hwk; rw [← hwk]; exact hrpfst x hx
        · rw [if_neg hi0] at hx; cases hx; exact hwk.symm
      · have hl : pageFlags pg = leafPageFlag := by simpa [readNRec, readNodeV] using hlf
        exact pageWs_pgid0 pg src' hl w' hw'
    · rename_i hyl
      split at hy
      · rename_i hyn
        cases hy
        subst hyn
        exact hframe y rp _ hrp rfl rfl rfl rfl rfl rfl rfl
      · exact hframe y ry ry hy rfl rfl rfl rfl rfl rfl rfl

theorem rblAcyc_addChild (ha : rblAcyc B) :
    rblAcyc (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') := by
  obtain ⟨ht, hh⟩ := ha
  have hlnl : l ≠ nl := by intro h; rw [h, hrp] at hfresh; cases hfresh
  have hns' := nodeAdded_ns B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp
  have hpar : ∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ null → ry.nv.parent' ≠ l := by
    intro y ry hy hp he
    obtain ⟨rq, hrq, -⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
    rw [he, hfresh] at hrq; cases hrq
  refine ⟨fun x => if x = l then 0 else ht x + 1, fun y ry hy hp => ?_⟩
  rw [hns'] at hy
  split at hy
  · rename_i hyl
    cases hy
    show (if y = l then 0 else ht y + 1) < (if nl = l then 0 else ht nl + 1)
    rw [if_pos hyl, if_neg (Ne.symm hlnl)]; omega
  · rename_i hyl
    split at hy
    · rename_i hyn
      cases hy; subst hyn
      have := hh y rp hrp hp
      show (if y = l then 0 else ht y + 1) < (if rp.nv.parent' = l then 0 else ht rp.nv.parent' + 1)
      rw [if_neg hyl, if_neg (hpar y rp hrp hp)]; omega
    · have := hh y ry hy hp
      show (if y = l then 0 else ht y + 1) < (if ry.nv.parent' = l then 0 else ht ry.nv.parent' + 1)
      rw [if_neg hyl, if_neg (hpar y ry hy hp)]; omega

theorem rblHt_addChild (ha : rblHt W B) :
    rblHt W (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') := by
  obtain ⟨ht, pht, hp, hh⟩ := ha
  have hns' := nodeAdded_ns B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp
  have hnsB := ns_addChild B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp hfresh
  have hnm' := nm_addChild W hwm bl B hv hc nl rp i w hrp hbr hw hnone l pg hpg p s cs' src'
  have hfree := free_addChild W hwm bl B hv hc nl rp i w hrp hbr hw hnone l pg hpg p s cs' src'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrp12, -⟩ := hc.2.2.2.2.2.2.2.1 nl rp hrp
  obtain ⟨-, -, hkids⟩ := hrp12 hbr
  obtain ⟨-, -, hcwf⟩ := hkids w (List.mem_of_getElem? hw)
  have hwf := hcwf hnone
  obtain ⟨-, -, -, hkind⟩ := treeWF_page _ _ _ pg hwf hpg
  have hold : ∀ y ry, B.ns !! y = some ry → y ≠ l := by
    intro y ry hy he; rw [he, hfresh] at hy; cases hy
  -- an old node's entry, in the grown bucket
  have hent : ∀ y ry, B.ns !! y = some ry → ry.nv.isLeaf' = false → ∀ w' ∈ ry.ws,
      (∀ l', (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').nm !! w'.pgid = some l' →
        (if l' = l then pht (uint.nat w.pgid) else ht l') + 1 = (if y = l then pht (uint.nat w.pgid) else ht y)) ∧
      ((nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').nm !! w'.pgid = none →
        pht (uint.nat w'.pgid) + 1 = (if y = l then pht (uint.nat w.pgid) else ht y)) := by
    intro y ry hy hb w' hw'
    rw [if_neg (hold y ry hy)]
    obtain ⟨a1, a2⟩ := (hh y ry hy).2 hb w' hw'
    refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
    · rw [hnm'] at hl'
      split at hl'
      · rename_i he
        cases hl'
        rw [if_pos rfl, ← he]; exact a2 (by rw [he]; exact hnone)
      · rename_i he
        obtain ⟨-, r0, hr0, -⟩ := hc.2.2.2.2.1 _ _ hl'
        rw [if_neg (hold l' r0 hr0)]; exact a1 l' hl'
    · rw [hnm'] at hn
      split at hn
      · cases hn
      · exact a2 hn
  refine ⟨fun x => if x = l then pht (uint.nat w.pgid) else ht x, pht, hp, fun y ry hy => ?_⟩
  rw [hns'] at hy
  split at hy
  · rename_i hyl
    cases hy; subst hyl
    have hpp := hp _ pg hpg
    refine ⟨fun hl => ?_, fun hb => ?_⟩
    · have hl' : pageFlags pg = leafPageFlag := by simpa [readNRec, readNodeV] using hl
      simp only [if_pos rfl]; exact hpp.1 hl'
    · have hbr' : pageFlags pg = branchPageFlag := by
        have : pageFlags pg ≠ leafPageFlag := by simpa [readNRec, readNodeV] using hb
        rcases hkind with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h this
        · exact h
      intro w' hw'
      obtain ⟨j, hj, rfl⟩ := pageWs_mem pg src' w' hw'
      have hnl' : pageFlags pg ≠ leafPageFlag := by rw [hbr']; exact branch_ne_leaf
      rw [(pageW_branch pg src' j hnl').2]
      have hcs : (W.pages !! branchPgid pg j).isSome := by
        rcases hkind with ⟨h, -⟩ | ⟨-, -, hch⟩
        · exact absurd h hnl'
        · cases hch j hj with
          | page _ cpg _ hcpg _ _ => rw [hcpg]; rfl
      have hn0 := hfree j hj hbr' hcs
      refine ⟨fun l' hl' => (by rw [hn0] at hl'; cases hl'), fun _ => ?_⟩
      simp only [if_pos rfl]
      rw [uint_nat_W64_w _ (branchPgid_lt pg j)]
      exact (hpp.2 hbr' j hj)
  · rename_i hyl
    split at hy
    · rename_i hyn
      cases hy; subst hyn
      refine ⟨fun hl => absurd hl (by rw [hbr]; nofun), fun _ => ?_⟩
      exact hent y rp hrp hbr
    · refine ⟨fun hl => ?_, fun hb => hent y ry hy hb⟩
      show (if y = l then pht (uint.nat w.pgid) else ht y) = 0
      rw [if_neg hyl]; exact (hh y ry hy).1 hl

end child

end pure

section res
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

open Iris.ProofMode in
/-- What `b.node` of the entry `i` of the branch node `nl` did (`nodeRes`) during rebalance:
the bucket stays in the invariant, its tokens and nested buckets' entries stay, the node `l` is
the position's, under `nl`; no node is newly unbalanced. -/
theorem rbl_nodeRes (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (dfc : Option Loc)
    (pm : GMap w64 Loc) (nl : Loc) (rp : NRec) (i : Nat) (w : WEntry) (p : Loc) (pg : List w8)
    (src : Src) (l : Loc) (B' : BRec) (st st' : go_etcd_io.bbolt.TxStats) (hv : viewOK W)
    (HB : rblB W hwm bl B dfc) (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false)
    (hw : rp.ws[i]? = some w) (hsrc : B.nm !! w.pgid = none → nodeSrcOK W B pm w.pgid p pg src)
    (hres : nodeRes B bl w.pgid nl p pg src l B' st st') :
    bktToks (GF := GF) γ W B ⊢ bktToks γ W B' ∗
      ⌜rblB W hwm bl B' dfc ∧ (∀ k v, entryIn W B k v → entryIn W B' k v) ∧
        B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.bm = B.bm ∧ B'.nm !! w.pgid = some l ∧
        (∃ rl, B'.ns !! l = some rl ∧ rl.nv.parent' = nl) ∧
        (∀ y ry', B'.ns !! y = some ry' → ry'.nv.unbalanced' = true →
          ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid') ∧
        (∀ y ry, B.ns !! y = some ry → ∃ ry', B'.ns !! y = some ry' ∧ ry'.ws = ry.ws ∧
          ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.nv.parent' = ry.nv.parent' ∧
          ry'.nv.unbalanced' = ry.nv.unbalanced' ∧ ry'.nv.pgid' = ry.nv.pgid')⌝ := by
  obtain ⟨hc, ⟨bnd, hk⟩, ha, hht⟩ := HB
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 nl rp hrp; rw [hbr] at this; cases this
  have hnl : nl ≠ null := by
    obtain ⟨-, -, -, -, -, -, h7, -⟩ := hc.2.2.2.2.2.2.2.1 nl rp hrp
    exact (hc.2.2.2.2.1 _ _ h7).1
  rcases hres with ⟨hk0, rfl, rfl⟩ | ⟨hk0, hfresh, hl, hst, s, cs', src', hs1, hs2, rfl⟩
  · iintro H
    iframe
    ipureintro
    obtain ⟨-, rl, hrl, -⟩ := hc.2.2.2.2.1 _ _ hk0
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := hc.2.2.2.2.2.2.2.1 nl rp hrp
    obtain ⟨-, -, hkids⟩ := h12 hbr
    obtain ⟨rl', hrl', hpl⟩ := (hkids w (List.mem_of_getElem? hw)).2.1 l hk0
    exact ⟨⟨hc, ⟨bnd, hk⟩, ha, hht⟩, fun _ _ h => h, rfl, rfl, rfl, hk0, ⟨rl', hrl', hpl⟩,
      fun y ry' hy hu => ⟨ry', hy, hu, rfl⟩,
      fun y ry hy => ⟨ry, hy, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hsrc' := hsrc hk0
  have hpg : W.pages !! uint.nat w.pgid = some pg := (hsrc'.2.2.2 (hc.2.2.2.2.2.1 hroot)).2.2.1
  have hcs := childStep W hwm bl B hv hc nl rp hrp hbr i w hw hnl p pg src l
    (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') st st'
    (fun h => ⟨hpg, (hsrc'.2.2.2 (hc.2.2.2.2.2.1 hroot)).2.1⟩)
    (Or.inr ⟨hk0, hfresh, hl, hst, s, cs', src', hs1, hs2, rfl⟩)
  iintro H
  iframe
  isplitl [H]
  · iapply bktToks_addChild γ W hwm bl B hv hc nl rp i w hrp hbr hw hk0 l hfresh hnl pg hpg
      p s cs' src' $$ H
  ipureintro
  have hns' := nodeAdded_ns B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp
  have hnsB := ns_addChild B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp hfresh
  refine ⟨⟨hcs.1, ⟨_, rblKeys_addChild W hwm bl B hv hc nl rp i w hrp hbr hw hk0 l hfresh hnl pg hpg
      p s cs' src' hsrc'.1 bnd dfc hk⟩, rblAcyc_addChild W hwm bl B hv hc nl rp i w hrp hbr hw hk0 l
      hfresh hnl pg hpg p s cs' src' ha, rblHt_addChild W hwm bl B hv hc nl rp i w hrp hbr hw hk0 l
      hfresh hnl pg hpg p s cs' src' hht⟩,
    entryIn_addChild W hwm bl B hv hc nl rp i w hrp hbr hw hk0 l hfresh hnl pg hpg p s cs' src',
    by simp [nodeAdded, hnl], rfl, rfl, by show (<[w.pgid := l]> B.nm) !! w.pgid = _; rw [GMap.lookup_insert],
    ⟨_, by rw [hns', if_pos rfl], rfl⟩, fun y ry' hy hu => ?_, fun y ry hy => ?_⟩
  · rw [hns'] at hy
    split at hy
    · cases hy; simp [readNRec, readNodeV] at hu
    · split at hy
      · rename_i hyl hyn
        cases hy; subst hyn
        exact ⟨rp, hrp, hu, rfl⟩
      · exact ⟨ry', hy, hu, rfl⟩
  · obtain ⟨ry', a1, a2, a3, a4, -, -, a7, a8⟩ := hnsB y ry hy
    exact ⟨ry', a1, a2, a3, a4, a8, a7⟩

end res

end bbolt
end EtcdGrove
end Perennial
