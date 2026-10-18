/-
`Bucket.rebalance` over the transaction: its buckets in the rebalance's invariant (`rblTxOK`), what
a rebalance of a bucket and of its nested buckets did (`rblTxRel`), reachability back through
it, and a bucket's tokens out of `txShapeR` and back.
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceWP
public import Proof.go_etcd_io.bbolt.RebalanceDB

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- Every bucket of the transaction in the rebalance's invariant, with no deficient node. -/
def rblTxOK (W : WView) (hwm : Nat) (T : WTx) : Prop :=
  ∀ bl B, T.bs !! bl = some B → rblB W hwm bl B none

/-- What a rebalance did to the transaction: no field but the stats and the buckets' nodes (no
node newly unbalanced), and the entries of nested buckets stay. -/
def rblTxRel (W : WView) (T T' : WTx) : Prop :=
  wtxSame T T' ∧ rblTxStep T T' ∧
    ∀ b B B', T.bs !! b = some B → T'.bs !! b = some B' → ∀ k v, entryIn W B k v → entryIn W B' k v

theorem rblTxRel_refl (W : WView) (T : WTx) : rblTxRel W T T := by
  refine ⟨⟨rfl, rfl, rfl, fun _ => rfl, T.t.stats', rfl⟩, fun b B' h => ⟨B', h, rfl, rfl, rfl,
    fun l r' hl hu => ⟨r', hl, hu⟩⟩, fun b B B' h h' k v he => ?_⟩
  rw [h] at h'; cases h'; exact he

theorem rblTxRel_trans (W : WView) (T1 T2 T3 : WTx) (h1 : rblTxRel W T1 T2) (h2 : rblTxRel W T2 T3) :
    rblTxRel W T1 T3 := by
  obtain ⟨s1, t1, e1⟩ := h1
  obtain ⟨s2, t2, e2⟩ := h2
  refine ⟨wtxSame_trans _ _ _ s1 s2, fun b B3 h3 => ?_, fun b B1 B3 hb1 hb3 k v he => ?_⟩
  · obtain ⟨B2, h2', a2, b2, c2, d2⟩ := t2 b B3 h3
    obtain ⟨B1, h1', a1, b1, c1, d1⟩ := t1 b B2 h2'
    refine ⟨B1, h1', a2.trans a1, b2.trans b1, c2.trans c1, fun l r3 hl hu => ?_⟩
    obtain ⟨r2, hr2, hu2⟩ := d2 l r3 hl hu
    exact d1 l r2 hr2 hu2
  · obtain ⟨B2, h2', -⟩ := t2 b B3 hb3
    exact e2 b B2 B3 h2' hb3 k v (e1 b B1 B2 hb1 h2' k v he)

/-- One bucket's rebalance. -/
theorem rblTxRel_upd (W : WView) (T : WTx) (st : TxStats) (bl : Loc) (B B' : BRec)
    (hB : T.bs !! bl = some B) (hbv : B'.bv = B.bv) (hib : B'.ib = B.ib) (hbm : B'.bm = B.bm)
    (hun : ∀ l r', B'.ns !! l = some r' → r'.nv.unbalanced' = true →
      ∃ r, B.ns !! l = some r ∧ r.nv.unbalanced' = true)
    (hent : ∀ k v, entryIn W B k v → entryIn W B' k v) :
    rblTxRel W T (wtxUpd T st bl B') := by
  refine ⟨wtxSame_upd T st bl B B' hB, fun b B2 h2 => ?_, fun b B1 B2 h1 h2 k v he => ?_⟩
  · change (<[bl := B']> T.bs) !! b = some B2 at h2
    by_cases hb : b = bl
    · subst hb; rw [GMap.lookup_insert] at h2; cases h2
      exact ⟨B, hB, hbv, hib, hbm, hun⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hb)] at h2
      exact ⟨B2, h2, rfl, rfl, rfl, fun l r' hl hu => ⟨r', hl, hu⟩⟩
  · change (<[bl := B']> T.bs) !! b = some B2 at h2
    by_cases hb : b = bl
    · subst hb; rw [GMap.lookup_insert] at h2; cases h2; rw [hB] at h1; cases h1; exact hent k v he
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hb)] at h2; rw [h1] at h2; cases h2; exact he

theorem rblTxOK_upd (W : WView) (hwm : Nat) (T : WTx) (st : TxStats) (bl : Loc) (B' : BRec)
    (h : rblTxOK W hwm T) (hB' : rblB W hwm bl B' none) : rblTxOK W hwm (wtxUpd T st bl B') := by
  intro b B2 h2
  change (<[bl := B']> T.bs) !! b = some B2 at h2
  by_cases hb : b = bl
  · subst hb; rw [GMap.lookup_insert] at h2; cases h2; exact hB'
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hb)] at h2; exact h b B2 h2

/-- A bucket reachable after a rebalance was reachable before (the buckets' maps stay). -/
theorem bktReach_back (W : WView) (T T' : WTx) (h : rblTxRel W T T') (a d : Loc)
    (hr : bktReach T' a d) : bktReach T a d := by
  induction hr with
  | root => exact .root
  | child bl B' name c _ hB' hbm ih =>
    obtain ⟨B, hB, -, -, e, -⟩ := h.2.1 bl B' hB'
    exact .child bl B name c ih hB (by rw [← e]; exact hbm)

/-- A bucket reachable from `b` is `b` or reachable from one of its nested buckets. -/
theorem bktReach_split (T : WTx) (b d : Loc) (hr : bktReach T b d) :
    d = b ∨ ∃ B name c, T.bs !! b = some B ∧ B.bm !! name = some c ∧ bktReach T c d := by
  induction hr with
  | root => exact Or.inl rfl
  | child bl B name c _ hB hbm ih =>
    rcases ih with rfl | ⟨B0, n0, c0, hB0, hbm0, hr0⟩
    · exact Or.inr ⟨B, name, c, hB, hbm, .root⟩
    · exact Or.inr ⟨B0, n0, c0, hB0, hbm0, .child bl B name c hr0 hB hbm⟩

theorem balancedFrom_rel (W : WView) (T T' : WTx) (h : rblTxRel W T T') (c : Loc)
    (hb : balancedFrom T c) : balancedFrom T' c := by
  intro d hr C' hC' l r' hl
  rcases Bool.eq_false_or_eq_true r'.nv.unbalanced' with hu | hu
  · obtain ⟨C, hC, -, -, -, hun⟩ := h.2.1 d C' hC'
    obtain ⟨r, hr', hu'⟩ := hun l r' hl hu
    have := hb d (bktReach_back W T T' h c d hr) C hC l r hr'
    rw [hu'] at this; cases this
  · exact hu

/-- The nested buckets' facts after a bucket's rebalance. -/
theorem bktNested_upd (W : WView) (T : WTx) (st : TxStats) (bl : Loc) (B B' : BRec)
    (hB : T.bs !! bl = some B) (hbv : B'.bv = B.bv) (hib : B'.ib = B.ib)
    (X X' : BRec) (hX : bktNested W T X) (hbmX : X'.bm = X.bm)
    (hentX : ∀ k v, entryIn W X k v → entryIn W X' k v) :
    bktNested W (wtxUpd T st bl B') X' := by
  intro k c hk
  rw [hbmX] at hk
  obtain ⟨C, v, hC, he, hl, hr, hn⟩ := hX k c hk
  by_cases hc : c = bl
  · subst hc; rw [hB] at hC; cases hC
    refine ⟨B', v, ?_, hentX k v he, hl, by rw [hib]; exact hr, fun h0 => ?_⟩
    · show (<[c := B']> T.bs) !! c = some B'; rw [GMap.lookup_insert]
    · rw [hib]; exact hn (by rw [← hbv]; exact h0)
  · refine ⟨C, v, ?_, hentX k v he, hl, hr, hn⟩
    show (<[bl := B']> T.bs) !! c = some C
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hc)]; exact hC

/-- A key of the loop's list other than the one at `i`, among those from `i`, is among those
after it. -/
theorem rb_mem_drop_succ (keys : List w64) (i : Nat) (key : w64) (hk : keys[i]? = some key) (p : w64)
    (h : p ∈ keys.drop i) (hne : p ≠ key) : p ∈ keys.drop (i + 1) := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hk
  rw [List.drop_eq_getElem_cons hlt, heq] at h
  rcases List.mem_cons.1 h with h | h
  · exact absurd h hne
  · exact h

/-- The bucket `bl` of `T` has no unbalanced node. -/
def bktBal (T : WTx) (bl : Loc) : Prop :=
  ∀ B, T.bs !! bl = some B → ∀ l r, B.ns !! l = some r → r.nv.unbalanced' = false

theorem bktBal_rel (W : WView) (T T' : WTx) (h : rblTxRel W T T') (bl : Loc) (hb : bktBal T bl) :
    bktBal T' bl := by
  intro B' hB' l r' hl
  rcases Bool.eq_false_or_eq_true r'.nv.unbalanced' with hu | hu
  · obtain ⟨B, hB, -, -, -, hun⟩ := h.2.1 bl B' hB'
    obtain ⟨r, hr, hu'⟩ := hun l r' hl hu
    have := hb B hB l r hr; rw [hu'] at this; cases this
  · exact hu

/-- A bucket's record after a rebalance: the same struct and nested buckets. -/
theorem rblTxRel_at (W : WView) (T T' : WTx) (h : rblTxRel W T T') (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) : ∃ B', T'.bs !! bl = some B' ∧ B'.bv = B.bv ∧ B'.ib = B.ib ∧
      B'.bm = B.bm := by
  obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 (show (T'.bs !! bl).isSome by
    rw [h.1.2.2.2.1 bl, hB]; rfl)
  obtain ⟨B0, hB0, e1, e2, e3, -⟩ := h.2.1 bl B' hB'
  rw [hB] at hB0; cases hB0
  exact ⟨B', hB', e1, e2, e3⟩

/-- At `Commit`: the transaction's buckets in the rebalance's invariant, from `rblReady`. -/
theorem rblTxOK_of_ready (W : WView) (txl rl : Loc) (T : WTx) (hc : txClean W txl rl T)
    (hr : rblReady W T) : rblTxOK W (uint.nat T.mv.pgid') T := by
  intro bl B hB
  obtain ⟨⟨bnd, hk, hf⟩, hp, ha, hh⟩ := hr bl B hB
  exact ⟨(hc.2.2.2.2.2.2.2 bl B hB).2.1, ⟨bnd, rblKeysB_of W B bnd hk hf hp⟩, ha, hh⟩

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A bucket but its nodes map. -/
def bktOwnNN (W : WView) (bl : Loc) (B : BRec) : IProp GF :=
  iprop(bl ↦ B.bv ∗ B.bv.InBucket' ↦ B.ib ∗ B.bv.buckets' ↦$ B.bm ∗
    pageOwn W B ∗ [∗map] l ↦ r ∈ B.ns, nodeOwn W l r)

open Iris.ProofMode in
theorem bktOwn_NN (W : WView) (bl : Loc) (B : BRec) :
    bktOwn (GF := GF) W bl B ⊣⊢ bktOwnNN W bl B ∗ B.bv.nodes' ↦$ B.nm := by
  unfold bktOwn bktOwnNN
  constructor
  · iintro ⟨H1, H2, H3, H4, H5, H6⟩; iframe
  · iintro ⟨⟨H1, H2, H4, H5, H6⟩, H3⟩; iframe

open Iris.ProofMode in
/-- The nested buckets' map of the bucket `bl` out of the transaction, and back. -/
theorem ownWriteTx_bm (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (B Bx : BRec)
    (hB : T.bs !! bl = some Bx) (hbv : Bx.bv = B.bv) (hbm : Bx.bm = B.bm) :
    ownWriteTx (GF := GF) W txl T ⊢ B.bv.buckets' ↦$ B.bm ∗
      (B.bv.buckets' ↦$ B.bm -∗ ownWriteTx W txl T) := by
  unfold ownWriteTx ownWriteTxG
  iintro ⟨⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, %Hok⟩
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
    (show Std.get? T.bs bl = some Bx from hB)).1 $$ Hbs with ⟨Hb, Hback⟩
  icases (bktOwn_NN W bl Bx).1 $$ Hb with ⟨Hb, H4⟩
  isimp only [bktOwnNN] at Hb
  icases Hb with ⟨H1, H2, H3, H5, H6⟩
  rw [← hbv, ← hbm]
  iframe H3
  iintro H3
  ihave Hbs := Hback $$ [H1 H2 H3 H4 H5 H6]
  · unfold bktOwn; iframe
  iframe
  ipureintro; exact Hok


open Iris.ProofMode in
/-- A bucket's tokens out of `txShapeR`, and back for the bucket changed by a rebalance. -/
theorem txShapeR_acc (γ : GName) (W : WView) (T : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) :
    txShapeR (GF := GF) γ W T ⊢ bktToks γ W B ∗
      (∀ (st : TxStats) (B' : BRec),
        ⌜rblKeys W B' ∧ B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.bm = B.bm ∧
          (∀ k v, entryIn W B k v → entryIn W B' k v)⌝ -∗
        bktToks γ W B' -∗ txShapeR γ W (wtxUpd T st bl B')) := by
  unfold txShapeR
  iintro ⟨%M, Ha, %HM, Hts, %Hk⟩
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun _ B => bktToks (GF := GF) γ W B)
    (show Std.get? T.bs bl = some B from hB)) $$ Hts with ⟨Ht, Hback⟩
  iframe Ht
  iintro %st %B' %HB' Ht
  obtain ⟨hk', hbv, hib, hbm, hent⟩ := HB'
  ihave Hts := Hback $$ %B' Ht
  iexists M
  rw [show (wtxUpd T st bl B').bs = <[bl := B']> T.bs from rfl]
  iframe
  ipureintro
  refine ⟨HM, fun b B2 h2 => ?_⟩
  change (<[bl := B']> T.bs) !! b = some B2 at h2
  by_cases hb : b = bl
  · subst hb; rw [GMap.lookup_insert] at h2; cases h2
    exact ⟨hk', bktNested_upd W T st _ B _ hB hbv hib B _ (Hk _ B hB).2 hbm hent⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hb)] at h2
    exact ⟨(Hk b B2 h2).1, bktNested_upd W T st bl B B' hB hbv hib B2 B2 (Hk b B2 h2).2 rfl
      (fun _ _ h => h)⟩


open Iris.ProofMode in
/-- At `Commit`: `txShape` gives `txShapeR` (`rblReady`). -/
theorem txShapeR_of (γ : GName) (W : WView) (T : WTx) (hr : rblReady W T) :
    txShape (GF := GF) γ W T ⊢ txShapeR γ W T := by
  unfold txShape txShapeR
  iintro ⟨%M, Ha, %HM, Hts, %Hk⟩
  iexists M
  iframe
  ipureintro
  refine ⟨HM, fun bl B hB => ?_⟩
  obtain ⟨⟨bnd, hk, hf⟩, hp, -, -⟩ := hr bl B hB
  exact ⟨⟨bnd, rblKeysB_of W B bnd hk hf hp⟩, (Hk bl B hB).2⟩

end own

end bbolt
end EtcdGrove
end Perennial
