/-
A nested bucket opened in a write transaction (`Bucket.Bucket`, `CreateBucket`): the value a
writer's cursor found for it (`kvSrc_bkt`: of a page of the view, or a persistent node entry),
its bytes lent out (`bktVal_acc`), the opened bucket's record (`childRec`, clean:
`bktClean_child`), and the transaction with the bucket added (`ownWriteTx_bkt_add`).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxAcc
public import Spec.go_etcd_io.bbolt.Bucket__openBucket_w

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- The transaction grew: its buckets' records may change and buckets be added. -/
def wtxSub (T T' : WTx) : Prop :=
  T'.mv = T.mv ∧ T'.pm = T.pm ∧ T'.bufs = T.bufs ∧
  (∀ b, (T.bs !! b).isSome → (T'.bs !! b).isSome) ∧ ∃ st, T'.t = { T.t with stats' := st }

theorem wtxSub_of_same (T T' : WTx) (h : wtxSame T T') : wtxSub T T' := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨a, b, c, fun x hx => by rw [d]; exact hx, e⟩

/-- The transaction with the stats `st`, the bucket `bl`'s record `B'` and a new bucket `cl`. -/
def wtxAdd (T : WTx) (st : TxStats) (bl : Loc) (B' : BRec) (cl : Loc) (Bc : BRec) : WTx :=
  { T with t := { T.t with stats' := st }, bs := <[cl := Bc]> (<[bl := B']> T.bs) }

theorem wtxSub_add (T : WTx) (st : TxStats) (bl : Loc) (B B' : BRec) (cl : Loc) (Bc : BRec)
    (hB : T.bs !! bl = some B) : wtxSub T (wtxAdd T st bl B' cl Bc) := by
  refine ⟨rfl, rfl, rfl, ?_, st, rfl⟩
  intro b hb
  show ((<[cl := Bc]> (<[bl := B']> T.bs)) !! b).isSome
  by_cases h1 : b = cl
  · subst h1; rw [GMap.lookup_insert]; rfl
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h1)]
    by_cases h2 : b = bl
    · subst h2; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h2)]; exact hb

theorem txClean_add (W : WView) (txl rl : Loc) (T : WTx) (bl : Loc) (B B' : BRec) (st : TxStats)
    (cl : Loc) (Bc : BRec) (h : txClean W txl rl T) (hB : T.bs !! bl = some B)
    (hc : bktClean W (uint.nat T.mv.pgid') bl B') (htx : B'.bv.tx' = txl)
    (hbm : ∀ n c, B'.bm !! n = some c → c = cl ∨ (T.bs !! c).isSome)
    (hcc : bktClean W (uint.nat T.mv.pgid') cl Bc) (hctx : Bc.bv.tx' = txl) (hcbm : Bc.bm = ∅)
    (hfresh : T.bs !! cl = none) :
    txClean W txl rl (wtxAdd T st bl B' cl Bc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hne : cl ≠ bl := by intro e; rw [e, hB] at hfresh; cases hfresh
  have hs : ∀ b, (T.bs !! b).isSome → ((<[cl := Bc]> (<[bl := B']> T.bs)) !! b).isSome := by
    intro b hb
    by_cases e1 : b = cl
    · subst e1; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e1)]
      by_cases e2 : b = bl
      · subst e2; rw [GMap.lookup_insert]; rfl
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e2)]; exact hb
  refine ⟨h1, h2, h3, h4, h5, h6, hs _ h7, ?_⟩
  intro b0 B0 hb0
  change (<[cl := Bc]> (<[bl := B']> T.bs)) !! b0 = some B0 at hb0
  by_cases e1 : b0 = cl
  · subst e1
    rw [GMap.lookup_insert] at hb0; cases hb0
    refine ⟨hctx, hcc, fun name c hn => ?_⟩
    rw [hcbm] at hn; cases hn
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e1)] at hb0
    by_cases e2 : b0 = bl
    · subst e2
      rw [GMap.lookup_insert] at hb0; cases hb0
      refine ⟨htx, hc, fun name c hn => ?_⟩
      rcases hbm name c hn with rfl | hc'
      · show ((<[c := _]> (<[b0 := _]> T.bs)) !! c).isSome
        rw [GMap.lookup_insert]; rfl
      · exact hs c hc'
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e2)] at hb0
      obtain ⟨k1, k2, k3⟩ := h8 b0 B0 hb0
      exact ⟨k1, k2, fun name c hn => hs c (k3 name c hn)⟩

theorem bytesAt_drop (bs : List w8) (off : Nat) : bytesAt bs off (bs.length - off) = bs.drop off := by
  unfold bytesAt; rw [List.take_of_length_le (by simp)]

/-- The record of a bucket opened from the value `vb` (its header at `ibl`, inline page at `pgl`,
of the source `src`). -/
def childRec (txl ibl pgl : Loc) (bm nm : GoMap) (vb : List w8) (src : Src) : BRec :=
  ⟨wOpenedOf txl ibl pgl bm nm vb, ibOf vb, ∅, ∅, ∅, inlinePage vb, src⟩

theorem uint_nat_ibOf_root (vb : List w8) : uint.nat (ibOf vb).root' = inBucketRoot vb := by
  unfold ibOf uint.nat; simp only
  have := inBucketRoot_lt vb
  exact toNat_W64 _ this

/-- A bucket opened from a good value is clean. -/
theorem bktClean_child (W : WView) (hwm : Nat) (cl txl ibl pgl : Loc) (bm nm : GoMap)
    (vb : List w8) (src : Src) (hv : bvalOK W.pages hwm vb)
    (hpgl : inBucketRoot vb = 0 → pgl ≠ null)
    (hsrc : src = Src.view ∨ src = Src.own DFrac.discard) :
    bktClean W hwm cl (childRec txl ibl pgl bm nm vb src) := by
  have hr0 := ibOf_root_zero vb
  refine ⟨?_, ?_, fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0 _
    have h := hr0.1 h0
    refine ⟨?_, hsrc, hv.2 h⟩
    show (if inBucketRoot vb = 0 then pgl else null) ≠ null
    rw [if_pos h]; exact hpgl h
  · intro h0
    have hne : inBucketRoot vb ≠ 0 := fun h => h0 (hr0.2 h)
    rcases hv.1 with ⟨_, -, -, ht⟩ | ⟨_, -, h0', -⟩
    · refine ⟨?_, fun _ => ?_⟩
      · show uint.nat (ibOf vb).root' < hwm
        rw [uint_nat_ibOf_root]
        cases ht with
        | page _ _ hlt _ _ _ => exact hlt
      · show treeWF W.pages hwm (uint.nat (ibOf vb).root'); rw [uint_nat_ibOf_root]; exact ht
    · exact absurd h0' hne
  · intro h; exact absurd rfl h
  · intro c l h; simp [childRec] at h
  · intro h0
    have hne : inBucketRoot vb ≠ 0 := fun h => h0 (hr0.2 h)
    show (if inBucketRoot vb = 0 then pgl else null) = null
    rw [if_neg hne]
  · intro _ l r h; simp [childRec] at h
  · intro l r h; simp [childRec] at h
  · intro l1 i1 c1 l2 i2 c2 h1; obtain ⟨r, w, h, -⟩ := h1; simp [childRec] at h
  · intro l i c h1; obtain ⟨r, w, h, -⟩ := h1; simp [childRec] at h

/-- What a writer's cursor found, with a bucket's flag: a good value, of a page of the view or of
a node entry (whose source is the view or persistent). -/
theorem kvSrc_bkt (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hvw : viewOK W) (k v : GoSlice) (f : w32) (h : kvSrcOK W hwm B (k, v, f)) (hf : isBktFlag f) :
    (∃ vb, bvalOK W.pages hwm vb ∧ inViewAt W v vb) ∨
    (∃ (l : Loc) (r : NRec) (i : Nat) (it : Inode) (w : WEntry),
        B.ns !! l = some r ∧ r.ins[i]? = some it ∧ r.ws[i]? = some w ∧ it.value' = v ∧
        bvalOK W.pages hwm w.value ∧ (w.vs = Src.view ∨ w.vs = Src.own DFrac.discard)) := by
  rcases h with h0 | ⟨l, r, i, it, w, hr, hleaf, hit, hw, he, hfl, -, -⟩ |
    ⟨pid, p, pg, i, hpa, hinl, htree, hlen, hwf, hflp, hi, he⟩
  · simp only [Prod.mk.injEq] at h0
    rw [h0.2.2] at hf; exact absurd hf (by unfold isBktFlag; decide)
  · simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := hc.2.2.2.2.2.2.2.1 l r hr
    rw [hfl] at hf
    obtain ⟨hb, hvs⟩ := h11 hleaf w (List.mem_of_getElem? hw) hf
    exact Or.inr ⟨l, r, i, it, w, hr, hit, hw, rfl, hb, hvs⟩
  · left
    unfold kvResult at he
    rw [if_neg (by omega)] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    simp only [Int.toNat_natCast] at hf ⊢
    rw [isBktFlag_iff _ (by unfold leafFlags; exact leAt_lt _ _ 4)] at hf
    by_cases hr : B.ib.root' = W64 0
    · obtain ⟨-, -, hok⟩ := hinl hr
      have := (hok.2.2.2.2 i hi).2
      rw [hf] at this; exact absurd this (by unfold bucketLeafFlag; decide)
    · have ht := htree hr
      have hpa' := hpa
      unfold wpageAt at hpa'; rw [if_neg hr] at hpa'
      obtain ⟨pg', hpg, heq⟩ := Option.map_eq_some_iff.1 hpa'
      cases heq
      obtain ⟨-, -, -, hk⟩ := treeWF_page _ _ _ _ ht hpg
      rcases hk with ⟨-, -, hbw⟩ | ⟨hb, -, -⟩
      · refine ⟨_, ⟨hbw i hi hf, fun h0 => ((hvw.2.2.2.2.1 _ _ hpg).1 hflp i hi).2 hf h0⟩, ?_⟩
        have hb := (hwf.2.2.1 i hi).1
        have := inViewAt_sub W _ _ (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i)
          (inViewLoc_page W _ _ hpg) (by omega) (leAt_lt _ _ 4)
        exact this
      · rw [hb] at hflp; exact absurd hflp (by unfold branchPageFlag leafPageFlag; decide)

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- Two whole points-to of a bucket exclude each other. -/
theorem bucket_ptsto_excl (l : Loc) (a b : Bucket) : (l ↦ a : IProp GF) ∗ l ↦ b ⊢ False := by
  rw [typedPointsto_unseal_eq, typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef]
  iintro ⟨⟨⟨H1, -⟩, -⟩, ⟨⟨H2, -⟩, -⟩⟩
  iapply loc_ptsto_excl
  iframe

/-- A location whose bucket struct is held is not one of the buckets `bs`. -/
theorem bs_fresh (W : WView) (bs : GMap Loc BRec) (l : Loc) (v : Bucket) :
    ([∗map] bl ↦ B ∈ bs, bktOwn (GF := GF) W bl B) ∗ l ↦ v ⊢
      ⌜bs !! l = none⌝ ∗ ([∗map] bl ↦ B ∈ bs, bktOwn (GF := GF) W bl B) ∗ l ↦ v := by
  cases h : bs !! l with
  | none => iintro ⟨H, Hl⟩; iframe; ipureintro; rfl
  | some B =>
    iintro ⟨H, Hl⟩
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
      (show Std.get? bs l = some B from h)).1 $$ H with ⟨Hb, -⟩
    unfold bktOwn
    icases Hb with ⟨Hbv, -⟩
    iexfalso
    iapply bucket_ptsto_excl
    iframe

/-- `ownWriteTx_bkt_acc`, closing with a new bucket `cl` added. -/
theorem ownWriteTx_bkt_add (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) :
    ownWriteTx (GF := GF) W txl T ⊢
      ⌜viewOK W ∧ txClean W txl (structFieldRef Tx go!"root" txl) T⌝ ∗
      TxW_rest_root txl (DFrac.own 1) T.t ∗ T.t.meta' ↦ T.mv ∗ T.t.pages' ↦$ T.pm ∗ bktOwn W bl B ∗
      wView W ∗
      ((∀ (st : TxStats) (B' : BRec),
        ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧ B'.bm = B.bm⌝ -∗
        TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
        T.t.pages' ↦$ T.pm -∗ bktOwn W bl B' -∗ wView W -∗ ownWriteTx W txl (wtxUpd T st bl B')) ∧
      (∀ (st : TxStats) (B' : BRec) (cl : Loc) (Bc : BRec),
        ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧
          (∀ n c, B'.bm !! n = some c → c = cl ∨ (T.bs !! c).isSome) ∧
          bktClean W (uint.nat T.mv.pgid') cl Bc ∧ Bc.bv.tx' = txl ∧ Bc.bm = ∅⌝ -∗
        TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
        T.t.pages' ↦$ T.pm -∗ bktOwn W bl B' -∗ bktOwn W cl Bc -∗ wView W -∗
        ownWriteTx W txl (wtxAdd T st bl B' cl Bc))) := by
  unfold ownWriteTx ownWriteTxG
  iintro ⟨⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, %Hok⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hbs⟩
  isplitr
  · ipureintro; exact Hok
  iframe Hrest Hm Hpm Hb Hv
  isplit
  · iintro %st %B' %Hc3 Hrest Hm Hpm Hb Hv
    obtain ⟨Hcl, Htx, Hbm⟩ := Hc3
    unfold wtxUpd
    isplitl [Hrest Hm Hpm Hbufs Hb Hbs]
    · iframe
      iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)).2
      iframe
    iframe
    ipureintro
    exact ⟨Hok.1, txClean_upd W txl _ T bl B B' st Hok.2 hB Hcl Htx Hbm⟩
  iintro %st %B' %cl %Bc %Hc6 Hrest Hm Hpm Hb Hc Hv
  obtain ⟨Hcl, Htx, Hbm, Hcc, Hctx, Hcbm⟩ := Hc6
  ihave Hbs := (BigSepM.bigSepM_insert_delete (M := GMap Loc)
    (Φ := fun bl B => bktOwn (GF := GF) W bl B) (m := T.bs) (i := bl) (x := B')).2 $$ [Hb Hbs]
  · iframe
  isimp only [bktOwn] at Hc
  icases Hc with ⟨Hcbv, Hcrest⟩
  icases bs_fresh W (<[bl := B']> T.bs) cl Bc.bv $$ [Hbs Hcbv] with ⟨%Hfr, Hbs, Hcbv⟩
  · iframe
  have Hfr' : T.bs !! cl = none := by
    have hne : cl ≠ bl := by
      intro e; subst e; rw [GMap.lookup_insert] at Hfr; cases Hfr
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)] at Hfr; exact Hfr
  unfold wtxAdd
  isplitl [Hrest Hm Hpm Hbufs Hbs Hcbv Hcrest]
  · iframe
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
      (show Std.get? (<[bl := B']> T.bs) cl = none from Hfr)).2
    iframe
    unfold bktOwn; iframe
  iframe
  ipureintro
  exact ⟨Hok.1, txClean_add W txl _ T bl B B' st cl Bc Hok.2 hB Hcl Htx Hbm Hcc Hctx Hcbm Hfr'⟩

/-- A nested bucket's value, out of the view or a node entry (persistent), lent out; its source,
the inline page's source of a bucket opened in place. -/
theorem bktVal_acc (W : WView) (hc : W.data.locCar ≠ 0) (bl : Loc) (B : BRec) (v : GoSlice)
    (vb : List w8) (src : Src) (hsrc : src = Src.view ∨ src = Src.own DFrac.discard)
    (h : (src = Src.view ∧ inViewAt W v vb) ∨ (∃ (l : Loc) (r : NRec) (i : Nat) (it : Inode) (w : WEntry),
        B.ns !! l = some r ∧ r.ins[i]? = some it ∧ r.ws[i]? = some w ∧ it.value' = v ∧
        w.value = vb ∧ w.vs = src)) :
    pagesView (GF := GF) W.data W.ps W.q W.pages ∗ ([∗map] l ↦ r ∈ B.ns, nodeOwn W l r) ⊢ ∃ dq,
      □ srcOwn W v src vb ∗ v ↦*{dq} vb ∗
      (v ↦*{dq} vb -∗ pagesView W.data W.ps W.q W.pages ∗ [∗map] l ↦ r ∈ B.ns, nodeOwn W l r) := by
  iintro ⟨Hpv, Hb⟩
  rcases h with ⟨rfl, hin⟩ | ⟨l, r, i, it, w, hr, hit, hw, rfl, rfl, rfl⟩
  · icases srcBorrow W hc W.q v Src.view vb (by nofun) $$ [Hpv] with ⟨%dq, -, Hv, Hback⟩
    · iframe; unfold srcOwn; ipureintro; exact hin
    iexists dq
    isplitr
    · imodintro; unfold srcOwn; ipureintro; exact hin
    iframe Hv
    iintro Hv
    ihave Hb2 := Hback $$ Hv
    icases Hb2 with ⟨Hpv, -⟩
    iframe
  · icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
      (show Std.get? B.ns l = some r from hr)).1 $$ Hb with ⟨Hnd, Hback⟩
    isimp only [nodeOwn] at Hnd
    icases Hnd with ⟨Hn, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
    icases BigSepL2.bigSepL2_lookup_acc (Φ := fun _ it w => wOwn (GF := GF) W it w) hit hw $$ Hents
      with ⟨Hi, Hiback⟩
    unfold wOwn
    icases Hi with ⟨%Hp, Hk, Hval⟩
    rcases hsrc with hs | hs
    · rw [hs]
      unfold srcOwn
      icases Hval with %hin
      icases srcBorrow W hc W.q it.value' Src.view w.value (by nofun) $$ [Hpv] with ⟨%dq, -, Hv, Hvback⟩
      · iframe; unfold srcOwn; ipureintro; exact hin
      iexists dq
      isplitr
      · imodintro; ipureintro; exact hin
      iframe Hv
      iintro Hv
      ihave Hb2 := Hvback $$ Hv
      icases Hb2 with ⟨Hpv, -⟩
      iframe
      ihave Hents := Hiback $$ [Hk]
      · simp only
        isplitr
        · ipureintro; exact Hp
        iframe
        ipureintro; exact hin
      iapply Hback
      unfold nodeOwn wOwn srcOwn; iframe
    · rw [hs]
      unfold srcOwn
      icases Hval with #Hval
      iexists DFrac.discard
      isplitr
      · imodintro; iexact Hval
      iframe Hval
      iintro -
      iframe
      ihave Hents := Hiback $$ [Hk]
      · simp only
        isplitr
        · ipureintro; exact Hp
        iframe
        iframe #
      iapply Hback
      unfold nodeOwn wOwn srcOwn; iframe

/-- A slice's bytes past its first `n`. -/
theorem slice_drop_bytes (s : GoSlice) (dq : DFrac) (bs : List w8) (n : Nat) (hn : n ≤ bs.length)
    (hne : bs ≠ []) :
    (s ↦*{dq} bs : IProp GF) ⊢ bytesPointsto (s.ptr +ₗ (n : Int)) dq (bs.drop n) := by
  iintro Hs
  icases (ownSlice_bytes s bs dq hne).1 $$ Hs with ⟨Hb, -⟩
  icases (bytesPointsto_around s.ptr dq bs n (bs.length - n) (by omega)).1 $$ Hb with ⟨-, Hm, -⟩
  rw [bytesAt_drop]
  iexact Hm

/-- The inline page of a bucket opened from `vb`, at `pgl`, of the source `csrc`. -/
def inlPageOwn (W : WView) (pgl : Loc) (vb : List w8) (csrc : Src) : IProp GF :=
  if inBucketRoot vb = 0 then
    (match csrc with
      | .view => iprop(⌜inViewLoc W pgl (inlinePage vb)⌝)
      | .own dq => bytesPointsto pgl dq (inlinePage vb)
      | .stale => iprop(True))
  else iprop(True)

/-- The opened bucket's resources, as a bucket of the transaction. -/
theorem childRec_own (W : WView) (cl txl ibl pgl : Loc) (bm nm : GoMap) (vb : List w8) (csrc : Src) :
    (cl ↦ wOpenedOf txl ibl pgl bm nm vb : IProp GF) ∗ ibl ↦ ibOf vb ∗
      bm ↦$ (∅ : GMap GoString Loc) ∗ nm ↦$ (∅ : GMap w64 Loc) ∗ inlPageOwn W pgl vb csrc ⊢
      bktOwn W cl (childRec txl ibl pgl bm nm vb csrc) := by
  iintro ⟨Hc, Hib, Hbm, Hnm, Hpg⟩
  unfold bktOwn pageOwn childRec
  simp only
  iframe Hc
  unfold wOpenedOf
  simp only
  iframe Hib Hnm Hbm
  isplitl [Hpg]
  · unfold inlPageOwn
    by_cases hr : inBucketRoot vb = 0
    · simp only [hr, ↓reduceIte]
      by_cases hp : pgl = null
      · simp only [hp, ↓reduceIte]; ipureintro; trivial
      · simp only [hp, ↓reduceIte]
        cases csrc <;> iexact Hpg
    · simp only [hr, ↓reduceIte]; ipureintro; trivial
  · iapply BigSepM.bigSepM_empty.2
    iempintro

end own

end bbolt
end EtcdGrove
end Perennial
