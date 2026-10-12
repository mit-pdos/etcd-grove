/-
A nested bucket of a bucket, as `Bucket.Bucket` returns it: its view (`childView`), and its
`bktR` built from the parent's (`child_build`).

The child shares its parent's transaction and pages; its header is the 16 bytes of its value
(in the parent's page, or in a copy), its inline page (root 0) the rest. It takes a fraction of
the parent's transaction fields (`txPart`) and pages, and of its value's bytes, and gives them
back (the wand of `child_build`; `bktR_lend` lends them out of the parent's `bktR`).
-/
module

public import Proof.go_etcd_io.bbolt.BucketOpen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax]

/-- What a bucket's context says of its view (`bktCtx`, its values being the view's). -/
def ctxOK (V : BktView) : Prop :=
  V.bkt.nodes' = map.nil ∧ V.bkt.rootNode' = null ∧ V.txv.pages' = map.nil ∧
  (V.root = W64 0 → V.bkt.page' = V.ip) ∧ V.txv.db' ≠ null ∧ V.bkt.tx' = V.tx

/-- The view of the nested bucket with the value `v`, its header at `ibl`. -/
def childView (V : BktView) (v : List w8) (ibl : Loc) : BktView :=
  { V with root := W64 (inBucketRoot v : Int), ip := ibl +ₗ 16, ipg := inlinePage v,
           bkt := openedBucketOf V.tx ibl v, seq := W64 (leAt v 8 8 : Int) }

theorem flag_bit (n : Nat) (h : n < 2 ^ 32) (hf : W32 (n : Int) &&& W32 1 ≠ W32 0) :
    n % 2 = 1 := by
  have e : (W32 (n : Int) &&& W32 1).toNat = n % 2 := by
    rw [BitVec.toNat_and, toNat_W32 n h]
    simp [Nat.and_one_is_mod]
  have h2 := Nat.mod_two_eq_zero_or_one n
  rcases h2 with h0 | h1
  · exfalso; apply hf; apply BitVec.eq_of_toNat_eq; rw [e, h0]; rfl
  · exact h1

/-- A nested bucket of a well-formed bucket is well-formed (its value, `bucketWF`). -/
theorem nestedWF (V : BktView) (pid : w64) (p : Loc) (pg : List w8) (i : Nat)
    (htree : V.treeOK) (hwf : V.wfAt pid) (hpa : V.pageAt pid = some (p, pg))
    (hfl : pageFlags pg = leafPageFlag) (hi : i < pageCount pg)
    (hb : leafFlags pg i % 2 = bucketLeafFlag) : bucketWF V.pages V.hwm (leafValue pg i) := by
  unfold BktView.pageAt at hpa
  unfold BktView.treeOK at htree
  unfold BktView.wfAt at hwf
  by_cases hr : V.root = W64 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at hpa htree hwf
    rw [ite_eq_left_of_eq_true _ _ (eq_true hwf.1)] at hpa
    cases hpa
    obtain ⟨-, hpt⟩ := htree
    cases hpt with
    | leaf _ _ _ _ hk => exact hk i hi hb
    | branch _ _ hb' _ _ => rw [hfl] at hb'; exact absurd hb' (by decide)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at hpa hwf
    obtain ⟨pg', hlk, heq⟩ := Option.map_eq_some_iff.1 hpa
    cases heq
    cases hwf with
    | page root pg'' _ hlk' _ hpt =>
      rw [hlk] at hlk'; cases hlk'
      cases hpt with
      | leaf _ _ _ _ hk => exact hk i hi hb
      | branch _ _ hb' _ _ => rw [hfl] at hb'; exact absurd hb' (by decide)

/-- A well-formed nested bucket's value holds its header (and more, for an inline one). -/
theorem bucketWF_len (pages : GMap Nat (List w8)) (hwm : Nat) (v : List w8)
    (h : bucketWF pages hwm v) : 16 ≤ v.length ∧ (inBucketRoot v = 0 → 16 < v.length) := by
  cases h with
  | file _ h16 hr _ => exact ⟨h16, fun h0 => absurd h0 hr⟩
  | inline _ h16 _ _ hpt =>
    refine ⟨h16, fun _ => ?_⟩
    cases hpt with
    | leaf _ _ _ hw _ =>
      have := hw.2.1; have := hw.1; unfold elemOff at *; unfold inlinePage at *
      simp at *; omega
    | branch _ _ _ hw _ =>
      have := hw.2.2.1; have := hw.2.1; unfold elemOff at *; unfold inlinePage at *
      simp at *; omega

theorem childView_ok (V : BktView) (v : List w8) (ibl : Loc) (hok : V.ok) (hc : ibl.locCar ≠ 0)
    (hwf : bucketWF V.pages V.hwm v) :
    (childView V v ibl).ok ∧ (childView V v ibl).treeOK := by
  refine ⟨⟨hok.1, by simpa [childView, Loc.add] using hc, hok.2.2⟩, ?_⟩
  have hlt := inBucketRoot_lt v
  unfold BktView.treeOK
  simp only [childView]
  cases hwf with
  | file _ _ hr htw =>
    have : W64 (inBucketRoot v : Int) ≠ W64 0 := fun e => hr ((ibOf_root_zero v).1 e)
    simp only [this, ↓reduceIte]
    have e : uint.nat (W64 (inBucketRoot v : Int)) = inBucketRoot v := by unfold uint.nat; word
    rw [e]; exact htw
  | inline _ _ hr hfl hpt =>
    have : W64 (inBucketRoot v : Int) = W64 0 := (ibOf_root_zero v).2 hr
    simp only [this, ↓reduceIte]
    exact ⟨hfl, hpt⟩

theorem childView_ctxOK (V : BktView) (v : List w8) (ibl : Loc) (h : ctxOK V) :
    ctxOK (childView V v ibl) := by
  obtain ⟨-, -, hp, -, hdb, -⟩ := h
  refine ⟨rfl, rfl, hp, fun h0 => ?_, hdb, rfl⟩
  have : inBucketRoot v = 0 := (ibOf_root_zero v).1 h0
  simp only [childView, openedBucketOf]
  rw [ite_eq_left_of_eq_true _ _ (eq_true this)]

/-- The fraction of its parent's part a nested bucket takes. -/
def childQ (h : Qp) : Qp := if h.val ≤ 1 then h.half.half else (1 : Qp).half.half

theorem childQ_lt_one (h : Qp) : childQ h < 1 := by
  unfold childQ
  split
  · simp only [Qp.lt_iff, Qp.val_half] at *; have := h.2; grind
  · simp only [Qp.lt_iff, Qp.val_half]; have : (1 : Qp).val = 1 := rfl; grind

theorem childQ_split (h : Qp) : ∃ r, h = childQ h + (childQ h + r) := by
  have hlt : childQ h + childQ h < h := by
    unfold childQ
    split
    · simp only [Qp.lt_iff, Qp.val_half, Qp.val_add] at *; have := h.2; grind
    · simp only [Qp.lt_iff, Qp.val_half, Qp.val_add] at *; have : (1 : Qp).val = 1 := rfl; grind
  obtain ⟨r, hr⟩ := Qp.lt_iff_exists_add.1 hlt
  exact ⟨r, by rw [← hr]; simp only [Qp.ext_iff, Qp.val_add]; grind⟩

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A bucket's transaction fields and the database's (a part of its context). -/
def txPart (V : BktView) (q : Qp) : IProp GF :=
  iprop(Tx_rest_stats V.tx (DFrac.own q) V.txv ∗
    structFieldRef DB go!"data" V.txv.db' ↦{DFrac.own q} V.data ∗
    structFieldRef DB go!"pageSize" V.txv.db' ↦{DFrac.own q} V.ps)

/-- A bucket's context, its values the view's. -/
theorem bktCtx_explicit (bl : Loc) (V : BktView) (q : Qp) :
    bktCtx (GF := GF) bl V q ⊣⊢ bl ↦{DFrac.own q} V.bkt ∗
      V.bkt.InBucket' ↦{DFrac.own q} internal.common.InBucket.mk V.root V.seq ∗
      txPart V q ∗ ⌜ctxOK V⌝ := by
  unfold bktCtx txPart
  constructor
  · iintro ⟨%bv, %ib, %t, %dbl, Hb, Hib, Ht, Hd, Hps, %Hcx⟩
    obtain ⟨Hr, Hn, Hrn, Hdb, Hp, Hpg, Hdn, Htx, Hbv, Htv, Hsq⟩ := Hcx
    have Hib : ib = internal.common.InBucket.mk V.root V.seq := by
      cases ib; simp only at Hr Hsq; rw [Hr, Hsq]
    subst Hbv Htv Hib Hdb
    rw [Htx]
    iframe
    ipureintro; exact ⟨Hn, Hrn, Hp, Hpg, Hdn, Htx⟩
  · iintro ⟨Hb, Hib, ⟨Ht, Hd, Hps⟩, %Hc⟩
    obtain ⟨Hn, Hrn, Hp, Hpg, Hdn, Htx⟩ := Hc
    iexists V.bkt, internal.common.InBucket.mk V.root V.seq, V.txv, V.txv.db'
    rw [Htx]
    iframe
    ipureintro; exact ⟨rfl, Hn, Hrn, rfl, Hp, Hpg, Hdn, rfl, rfl, rfl, rfl⟩

/-- The view's pages, at `q`. -/
def viewPages (V : BktView) (q : Qp) : IProp GF := pagesView V.data (uint.nat V.ps) q V.pages

/-- A part of a bucket, lent out: its context and pages at `qc`, and the transaction's pages at
`qc` (besides its own for a bucket of file pages; its spare ones for an inline bucket). -/
theorem bktR_lend (bl : Loc) (V : BktView) (h qc r : Qp) (hq : h = qc + (qc + r)) :
    bktR (GF := GF) bl V h ⊢ ⌜V.ok ∧ V.treeOK⌝ ∗ bktCtx bl V qc ∗ bktPages V qc ∗ viewPages V qc ∗
      (bktCtx bl V qc -∗ bktPages V qc -∗ viewPages V qc -∗ bktR bl V h) := by
  unfold bktR viewPages
  by_cases hr : V.root = W64 0 <;> simp only [hr, ↓reduceIte]
  · iintro ⟨Hc, Hp, He, %Hok⟩
    icases (bktCtx_split _ _ qc (qc + r)).1 $$ [Hc] with ⟨Hc1, Hc2⟩
    · rw [← hq]; iexact Hc
    icases (bktPages_split _ qc (qc + r)).1 $$ [Hp] with ⟨Hp1, Hp2⟩
    · rw [← hq]; iexact Hp
    icases (pagesView_split _ _ _ qc (qc + r)).1 $$ [He] with ⟨He1, He2⟩
    · rw [← hq]; iexact He
    iframe Hc1 Hp1 He1
    isplitr
    · ipureintro; exact Hok
    iintro Hc1 Hp1 He1
    ihave Hc := (bktCtx_split _ _ qc (qc + r)).2 $$ [Hc1 Hc2]
    · iframe
    ihave Hp := (bktPages_split _ qc (qc + r)).2 $$ [Hp1 Hp2]
    · iframe
    ihave He := (pagesView_split _ _ _ qc (qc + r)).2 $$ [He1 He2]
    · iframe
    rw [hq]
    iframe
    ipureintro; exact Hok
  · iintro ⟨Hc, Hp, -, %Hok⟩
    icases (bktCtx_split _ _ qc (qc + r)).1 $$ [Hc] with ⟨Hc1, Hc2⟩
    · rw [← hq]; iexact Hc
    icases (bktPages_split _ qc (qc + r)).1 $$ [Hp] with ⟨Hp1, Hp2⟩
    · rw [← hq]; iexact Hp
    icases (bktPages_split _ qc r).1 $$ Hp2 with ⟨Hp2, Hp3⟩
    have Hbp : ∀ x, bktPages (GF := GF) V x = pagesView V.data (uint.nat V.ps) x V.pages := by
      intro x; unfold bktPages; rw [ite_eq_right_of_eq_false _ _ (eq_false hr)]
    rw [Hbp qc] at *
    iframe Hc1 Hp1 Hp2
    isplitr
    · ipureintro; exact Hok
    iintro Hc1 Hp1 Hp2
    ihave Hc := (bktCtx_split _ _ qc (qc + r)).2 $$ [Hc1 Hc2]
    · iframe
    rw [← Hbp qc] at *
    ihave Hp2 := (bktPages_split _ qc r).2 $$ [Hp2 Hp3]
    · iframe
    ihave Hp := (bktPages_split _ qc (qc + r)).2 $$ [Hp1 Hp2]
    · iframe
    rw [hq]
    iframe
    ipureintro; exact ⟨trivial, Hok⟩

/-- The nested bucket's `bktR`, from its struct, its value's bytes, and a part of its parent's
transaction fields and pages (given back by the wand). -/
theorem child_build (cl ibl : Loc) (V : BktView) (v : List w8) (qc : Qp) (hq1 : qc < 1)
    (hok : V.ok) (hctx : ctxOK V) (hwf : bucketWF V.pages V.hwm v) (hc : ibl.locCar ≠ 0) :
    cl ↦ openedBucketOf V.tx ibl v ∗ bytesPointsto (GF := GF) ibl (DFrac.own qc) v ∗ txPart V qc ∗
        viewPages V qc ⊢
      bktR cl (childView V v ibl) qc ∗
      (bktR cl (childView V v ibl) qc -∗
        bytesPointsto ibl (DFrac.own qc) v ∗ txPart V qc ∗ viewPages V qc) := by
  obtain ⟨rest, hrest⟩ := Qp.lt_iff_exists_add.1 hq1
  obtain ⟨h16, -⟩ := bucketWF_len _ _ _ hwf
  have hcv := childView_ok V v ibl hok hc hwf
  have hcc := childView_ctxOK V v ibl hctx
  iintro ⟨Hcl, Hv, Htx, Hpg⟩
  icases (pt_split' _ _ qc rest 1 hrest.symm).1 $$ Hcl with ⟨Hcl, -⟩
  icases (value_inbucket (hG := hG) ibl _ v h16 hc).1 $$ Hv with ⟨Hib, Hin⟩
  have Hib_eq : ibOf v = internal.common.InBucket.mk (childView V v ibl).root (childView V v ibl).seq :=
    rfl
  have Htx_eq : txPart (GF := GF) V qc = txPart (childView V v ibl) qc := rfl
  have Hpg_eq : viewPages (GF := GF) V qc = viewPages (childView V v ibl) qc := rfl
  have Hibl : (childView V v ibl).bkt.InBucket' = ibl := rfl
  rw [Hib_eq] at *
  rw [Htx_eq, Hpg_eq] at *
  unfold bktR
  by_cases hr : inBucketRoot v = 0
  · have hr' : (childView V v ibl).root = W64 0 := (ibOf_root_zero v).2 hr
    have hbp : bktPages (GF := GF) (childView V v ibl) qc =
        bytesPointsto (ibl +ₗ 16) (DFrac.own qc) (v.drop 16) := by
      unfold bktPages; rw [ite_eq_left_of_eq_true _ _ (eq_true hr')]; rfl
    simp only [hr', ↓reduceIte]
    rw [hbp]
    isplitl [Hcl Hib Htx Hin Hpg]
    · isplitl [Hcl Hib Htx]
      · iapply (bktCtx_explicit cl (childView V v ibl) qc).2
        rw [Hibl, show (childView V v ibl).bkt = openedBucketOf V.tx ibl v from rfl, hr']
        isplitl [Hcl]; · iexact Hcl
        isplitl [Hib]; · iexact Hib
        isplitl [Htx]; · iexact Htx
        ipureintro; exact hcc
      unfold viewPages
      iframe
      ipureintro; exact hcv
    iintro ⟨Hctx, Hin, Hpg, -⟩
    icases (bktCtx_explicit cl (childView V v ibl) qc).1 $$ Hctx with ⟨-, Hib, Htx, -⟩
    rw [← Hib_eq, Hibl]
    iframe Htx
    isplitl [Hib Hin]
    · iapply (value_inbucket (hG := hG) ibl _ v h16 hc).2
      iframe
    unfold viewPages
    iframe
  · have hr' : (childView V v ibl).root ≠ W64 0 := fun h => hr ((ibOf_root_zero v).1 h)
    have hbp : bktPages (GF := GF) (childView V v ibl) qc = viewPages (childView V v ibl) qc := by
      unfold bktPages; rw [ite_eq_right_of_eq_false _ _ (eq_false hr')]; rfl
    simp only [hr', ↓reduceIte]
    rw [hbp]
    isplitl [Hcl Hib Htx Hpg]
    · isplitl [Hcl Hib Htx]
      · iapply (bktCtx_explicit cl (childView V v ibl) qc).2
        rw [Hibl, show (childView V v ibl).bkt = openedBucketOf V.tx ibl v from rfl]
        isplitl [Hcl]; · iexact Hcl
        isplitl [Hib]; · iexact Hib
        isplitl [Htx]; · iexact Htx
        ipureintro; exact hcc
      iframe
      ipureintro; exact ⟨trivial, hcv⟩
    iintro ⟨Hctx, Hpg, -, -⟩
    icases (bktCtx_explicit cl (childView V v ibl) qc).1 $$ Hctx with ⟨-, Hib, Htx, -⟩
    rw [← Hib_eq, Hibl]
    iframe Htx Hpg
    iapply (value_inbucket (hG := hG) ibl _ v h16 hc).2
    iframe

end lemmas

end bbolt
end EtcdGrove
end Perennial
