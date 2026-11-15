/-
**The writer's page tokens across entry and bucket updates** (batch 37 item 14; `Inv/ShapeOps`):
- a node's record replaced with its tokens below (`txShape_setNode`), `node.put` of an entry that
  owns no tokens (`txShape_putAt`: a plain value, an inline bucket's value, an opened bucket's
  header) and `node.del` (`txShape_delAt`): U7's `Put`, `Delete`, `CreateBucket(IfNotExists)`,
  `DeleteBucket`; U9's `Bucket.spill` header puts;
- a bucket record replaced (`txShape_setBkt`: `CreateBucket`'s `b.page = nil`), `Bucket.free`'s
  records (`txTokL_bktFreed`), a bucket record removed (`txTokL_delBkt`: `DeleteBucket`'s child),
  a bucket entry un-opened once no entry of its name remains (`bktTokL_unopen`: `DeleteBucket`'s
  `delete(b.buckets, key)`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsView

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.Std go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

open Classical

/-- A plain leaf entry owns no tokens. -/
theorem entNoTok_plain (v : View) (B : BRec) (e : WEntry) (h : ¬ isBktFlag e.flags) :
    entNoTok v B true e := by
  unfold entNoTok entTokL; simp only [↓reduceIte]; rw [if_neg (fun h' => h h'.1)]

/-- An inline bucket's leaf entry owns no tokens. -/
theorem entNoTok_inline (v : View) (B : BRec) (e : WEntry) (h : inBucketRoot e.value = 0) :
    entNoTok v B true e := by
  unfold entNoTok entTokL; simp only [↓reduceIte]; rw [if_neg (fun h' => h'.2.1 h)]

/-- An opened bucket's leaf entry owns no tokens (its bucket record does). -/
theorem entNoTok_opened (v : View) (B : BRec) (e : WEntry) (h : opened B e.key) :
    entNoTok v B true e := by
  unfold entNoTok entTokL; simp only [↓reduceIte]; rw [if_neg (fun h' => h'.2.2 h)]

/-- A map's bindings mapped pointwise: its list is the mapped list. -/
theorem toList_pointwise_perm {K V : Type _} [DecidableEq K] (m m' : GMap K V)
    (F : K → V → V) (h : ∀ k, m' !! k = (m !! k).map (F k)) :
    (FiniteMap.toList m').Perm ((FiniteMap.toList m).map fun p => (p.1, F p.1 p.2)) := by
  have hkeys : ((FiniteMap.toList m).map fun p => (p.1, F p.1 p.2)).map Prod.fst =
      (FiniteMap.toList m).map Prod.fst := by rw [List.map_map]; rfl
  have hnd : ((FiniteMap.toList m).map fun p => (p.1, F p.1 p.2)).Nodup := by
    have := GMap.toList_keys_nodup m
    change (List.map Prod.fst (FiniteMap.toList m)).Nodup at this
    rw [← hkeys] at this
    exact List.Pairwise.of_map Prod.fst (fun a b h e => h (by rw [e])) this
  have hnd' : (FiniteMap.toList m').Nodup :=
    List.Pairwise.of_map Prod.fst (fun a b h e => h (by rw [e])) (GMap.toList_keys_nodup m')
  refine (List.perm_ext_iff_of_nodup hnd' hnd).2 fun ⟨k, x⟩ => ?_
  rw [List.mem_map]
  constructor
  · intro hx
    have := (GMap.mem_toList _ _ _).1 hx
    rw [h k] at this
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 this
    exact ⟨(k, y), (GMap.mem_toList _ _ _).2 hy, rfl⟩
  · rintro ⟨⟨k', y⟩, hy, e⟩
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine (GMap.mem_toList _ _ _).2 ?_
    rw [h k', (GMap.mem_toList _ _ _).1 hy]; rfl

/-- **`Bucket.free`'s records keep the tokens** (its header's root and the walked nodes' page ids
set to `0`: their pages' tokens dropped). For `DeleteBucket` (U7) and `Bucket.spill` (U9). -/
theorem txTokL_bktFreed (X X' : WX) (bl : Loc) (h : bktFreed X X' bl) :
    (txTokL X').Subperm (txTokL X) ∧ X'.v = X.v := by
  obtain ⟨B, ns', hB, rfl, hns⟩ := h
  refine ⟨txTokL_setBkt_sub X bl B _ hB ?_, rfl⟩
  unfold bktTokL
  show (if B.bv.rootNode' = null then (if W64 0 = W64 0 then [] else _) else _).Subperm _
  split
  · rw [if_pos rfl]; exact List.nil_subperm
  · refine ((flatMap_perm _ (toList_pointwise_perm B.ns ns' _ hns)).subperm).trans ?_
    rw [List.flatMap_map]
    refine flatMap_subperm _ _ _ fun ⟨l, r⟩ _ => ?_
    dsimp only
    rw [nodeTokL_congr X.v _ B _ rfl rfl]
    split
    · unfold nodeTokL ownTokL
      simp only [↓reduceIte]
      exact (List.sublist_append_right _ _).subperm
    · exact List.Subperm.refl _

/-- **A bucket record removed** (`DeleteBucket`'s child moved out of `bs`): its tokens dropped. -/
theorem txTokL_delBkt (X X' : WX) (c : Loc) (hbs : X'.t.bs = GMap.delete c X.t.bs)
    (hv : X'.v = X.v) : (txTokL X').Subperm (txTokL X) := by
  unfold txTokL bktsTokL; rw [hbs, hv]
  exact flatMap_delete_subperm _ _ _

/-- With no bucket entry named `n` under a page position, excluding `n` changes nothing. -/
theorem xHas_unopen {P : Pages} {op : List w8 → Prop} {n : List w8} {c : Nat}
    (hno : ∀ p pg i, ownHas P c p → P !! p = some pg → pageFlags pg = leafPageFlag →
      i < pageCount pg → leafFlags pg i % 2 = bucketLeafFlag → leafKey pg i ≠ n)
    {a id : Nat} (ha : ∀ p, ownHas P a p → ownHas P c p) (h : xHas P (fun k => op k ∧ k ≠ n) a id) :
    xHas P op a id := by
  induction h with
  | root root pg hpg => exact xHas.root root pg hpg
  | child root pg i id hpg hfl hi _ ih =>
    exact xHas.child root pg i id hpg hfl hi (ih fun p hp => ha p (ownHas.child root pg i p hpg hfl hi hp))
  | bucket root pg i id hpg hfl hi hb hop hbh =>
    refine xHas.bucket root pg i id hpg hfl hi hb (fun h' => hop ⟨h', ?_⟩) hbh
    exact hno root pg i (ha root (ownHas.root root pg hpg)) hpg hfl hi hb

/-- The bucket record with `n` no longer cached. -/
abbrev bUnopen (B : BRec) (n : List w8) : BRec := { B with bm := GMap.delete n B.bm }

theorem opened_bUnopen (B : BRec) (n : List w8) :
    opened (bUnopen B n) = fun k => opened B k ∧ k ≠ n := by
  funext k; apply propext
  unfold opened bUnopen
  by_cases e : k = n
  · subst e; simp
  · rw [GMap.lookup_delete_ne _ (Ne.symm e)]; simp [e]

/-- **Un-opening a bucket name that no entry holds** (`DeleteBucket`'s `delete(b.buckets, key)`,
once the entry is deleted: no bucket entry named `n` in `B`'s nodes or under its page positions,
`entryIn`): the tokens do not grow. -/
theorem bktTokL_unopen (vw : View) (B : BRec) (n : List w8) (hno : ∀ v, ¬ entryIn vw B n v) :
    (bktTokL vw (bUnopen B n)).Subperm (bktTokL vw B) := by
  have hpos : ∀ c, posRoot B c → ∀ p pg i, ownHas vw.pages c p → vw.pages !! p = some pg →
      pageFlags pg = leafPageFlag → i < pageCount pg → leafFlags pg i % 2 = bucketLeafFlag →
      leafKey pg i ≠ n := by
    intro c hc p pg i hown hpg hfl hi hb e
    exact hno _ (Or.inr ⟨c, p, pg, i, hc, hown, hpg, hfl, hi, e, hb, rfl⟩)
  have hx : ∀ c, posRoot B c → (pgIds (xPages vw.pages (opened (bUnopen B n)) c)).Subperm
      (pgIds (xPages vw.pages (opened B) c)) := by
    intro c hc
    rw [opened_bUnopen]
    exact pgIds_filter_subperm _ _ _ fun id _ _ h => decide_eq_true
      (xHas_unopen (hpos c hc) (fun p hp => hp) (of_decide_eq_true h))
  unfold bktTokL
  show (if B.bv.rootNode' = null then (if B.ib.root' = W64 0 then [] else _) else _).Subperm
    (if B.bv.rootNode' = null then (if B.ib.root' = W64 0 then [] else _) else _)
  split
  · rename_i hrn
    split
    · exact List.Subperm.refl _
    · rename_i hr0
      exact hx _ (Or.inl ⟨hrn, hr0, rfl⟩)
  · refine flatMap_subperm _ _ _ fun ⟨l, r⟩ hlr => ?_
    have hr : B.ns !! l = some r := (GMap.mem_toList _ _ _).1 hlr
    dsimp only
    unfold nodeTokL entsTokL
    refine (List.subperm_append_left _).2 (flatMap_subperm _ _ _ fun w hw => ?_)
    split
    · rename_i hlf
      unfold entTokL
      split
      · rename_i h
        have hk : w.key ≠ n := fun e => hno w.value (Or.inl ⟨l, r, w, hr, hlf, hw, e, h.1, rfl⟩)
        have : ¬ opened B w.key := fun ho => h.2.2 (by rw [opened_bUnopen]; exact ⟨ho, hk⟩)
        rw [if_pos ⟨h.1, h.2.1, this⟩]
      · exact List.nil_subperm
    · rename_i hlf
      unfold brTokL
      show (if B.nm !! w.pgid = none then _ else []).Subperm (if B.nm !! w.pgid = none then _ else [])
      split
      · rename_i hnm
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hw
        refine hx _ (Or.inr ⟨l, j, ⟨r, w, hr, by simpa using hlf, hj, ?_, ?_⟩, ?_⟩)
        · apply BitVec.eq_of_toNat_eq; simp
        · have e : W64 ((w.pgid.toNat : Nat) : Int) = w.pgid := by
            apply BitVec.eq_of_toNat_eq; simp
          rw [e]; exact hnm
        · exact w.pgid.isLt
      · exact List.Subperm.refl _

/-- A bucket record's tokens depend on its root node, header, caches and nodes only (not, e.g.,
its `page` field: `CreateBucket`'s `b.page = nil`). -/
theorem bktTokL_congr (v : View) (B B' : BRec) (hrn : B'.bv.rootNode' = B.bv.rootNode')
    (hib : B'.ib = B.ib) (hnm : B'.nm = B.nm) (hbm : B'.bm = B.bm) (hns : B'.ns = B.ns) :
    bktTokL v B' = bktTokL v B := by
  have hop : opened B' = opened B := by unfold opened; rw [hbm]
  unfold bktTokL
  rw [hrn, hib, hns, hop]
  simp only [nodeTokL_congr v B B' _ hnm hbm]

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **A bucket record replaced, its tokens below** (`CreateBucket`'s `b.page = nil`: equal). -/
theorem txShape_setBkt (γ : GName) (X : WX) (bl : Loc) (B B' : BRec) (extra : GMap Nat Unit)
    (hB : X.t.bs !! bl = some B) (h : (bktTokL X.v B').Subperm (bktTokL X.v B)) :
    txShape (GF := GF) γ X extra ⊢ txShape γ (X.setBkt bl B') extra :=
  txShape_sub γ X _ extra rfl fun _ => txTokL_setBkt_sub X bl B B' hB h

/-- **A node record replaced, its tokens below.** -/
theorem txShape_setNode (γ : GName) (X : WX) (bl l : Loc) (B : BRec) (r r' : NRec)
    (extra : GMap Nat Unit) (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r)
    (h : (nodeTokL X.v B r').Subperm (nodeTokL X.v B r)) :
    txShape (GF := GF) γ X extra ⊢ txShape γ (X.setNode bl l r') extra := by
  refine txShape_sub γ X _ extra ?_ fun _ => txTokL_setNode_sub X bl l B r r' hB hr h
  unfold WX.setNode; rw [hB]; rfl

/-- **`node.put` of an entry that owns no tokens** (`entNoTok_plain`, `entNoTok_inline`,
`entNoTok_opened`; `node.put`'s post). U7: `Put`, `CreateBucket(IfNotExists)`; U9: the root
bucket's header puts. -/
theorem txShape_putAt (γ : GName) (X : WX) (bl l : Loc) (B : BRec) (r : NRec) (s : GoSlice)
    (ins : List Inode) (k : List w8) (e : WEntry) (extra : GMap Nat Unit)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (he : entNoTok X.v B r.nv.isLeaf' e) :
    txShape (GF := GF) γ X extra ⊢
      txShape γ (X.setNode bl l (r.withEnts s ins (wsPutAt r.ws k e))) extra :=
  txShape_setNode γ X bl l B r _ extra hB hr
    (nodeTokL_withEnts_sub X.v B r s ins _ (entsTokL_wsPutAt_sub X.v B _ r.ws k e he))

/-- **`node.del`** (its post's `withEntsU … (wsDelAt r.ws k)`). U7: `Delete`, `DeleteBucket`. -/
theorem txShape_delAt (γ : GName) (X : WX) (bl l : Loc) (B : BRec) (r : NRec) (s : GoSlice)
    (ins : List Inode) (k : List w8) (u : Bool) (extra : GMap Nat Unit)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) :
    txShape (GF := GF) γ X extra ⊢
      txShape γ (X.setNode bl l (r.withEntsU s ins (wsDelAt r.ws k) u)) extra :=
  txShape_setNode γ X bl l B r _ extra hB hr
    (nodeTokL_withEntsU_sub X.v B r s ins _ u (entsTokL_wsDelAt_sub X.v B _ r.ws k))

/-- **`Bucket.free`** (its post's `bktFreed`). -/
theorem txShape_bktFreed (γ : GName) (X X' : WX) (bl : Loc) (extra : GMap Nat Unit)
    (h : bktFreed X X' bl) : txShape (GF := GF) γ X extra ⊢ txShape γ X' extra := by
  have ⟨hs, hv⟩ := txTokL_bktFreed X X' bl h
  exact txShape_sub γ X X' extra (by rw [hv]) fun _ => hs

/-- **`DeleteBucket`'s un-opening** (`bktTokL_unopen`; no bucket entry named `n` left in `B`). -/
theorem txShape_unopen (γ : GName) (X : WX) (bl : Loc) (B : BRec) (n : List w8)
    (extra : GMap Nat Unit) (hB : X.t.bs !! bl = some B) (hno : ∀ v, ¬ entryIn X.v B n v) :
    txShape (GF := GF) γ X extra ⊢ txShape γ (X.setBkt bl (bUnopen B n)) extra :=
  txShape_setBkt γ X bl B _ extra hB (bktTokL_unopen X.v B n hno)

/-- **A bucket record removed** (`DeleteBucket`'s child). -/
theorem txShape_delBkt (γ : GName) (X X' : WX) (c : Loc) (extra : GMap Nat Unit)
    (hbs : X'.t.bs = GMap.delete c X.t.bs) (hv : X'.v = X.v) :
    txShape (GF := GF) γ X extra ⊢ txShape γ X' extra :=
  txShape_sub γ X X' extra (by rw [hv]) fun _ => txTokL_delBkt X X' c hbs hv

end res

end bbolt
end EtcdGrove
end Perennial
