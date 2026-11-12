/-
**The flagged writer side** (batch 44.1 of `notes/bbolt-proof-plan.md`, U10g's finding, decided by
the coordinator): between `Commit`'s free of the old synced freelist page (`store_free_fl`) and the
publish or rollback, the page's own slots are pending for the writer's txid, which `flCurOK`'s
slot clause forbids. `wdbOK' true` relaxes that clause only (`flCurOKr`: a slot of the synced
page's extent may be pending, for the writer's txid only); `wdbOK' false` is `wdbOK`
(`wdbOK'_false`, by definition). `wdbW' fr` is `wdbW` with `wdbOK' fr` and the writer's
`fbTok` (the freed page's recorded bytes' half, which `store_publish` and `store_rollback` take):
`wdbW_wdbW'` (flag `false`, the token empty), `wdbW'_wdbW` (flag `false`, the token dropped).
Existing statements keep `wdbOK`/`wdbW`; the steps of `Commit` from the free on take the flagged
form.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
import Proof.go_etcd_io.bbolt.Txn.WJoin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **`flCurOK` with its slot clause relaxed** for the writer `wtx` (maintainer 13: the clause
of the page freed by `Commit`): a slot of the synced page's extent is not covered, is pending, and
not free and pending only for `wtx` (in place of "in no list"). Every other clause is
`flCurOK`'s. -/
def flCurOKr (fl : FLPg) (C : CommitSt) (wtx : w64) (pg : List w8) : Prop :=
  ∀ f, C.flpg = some f →
    2 ≤ f ∧ f + (1 + pageOverflow pg) ≤ C.hwm ∧ pg.length = (1 + pageOverflow pg) * 4096 ∧
    pageFlags pg = freelistPageFlag ∧
    16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length ∧
    (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ x.toNat) ∧
    (∀ x ∈ flIds pg, ¬ (f ≤ x.toNat ∧ x.toNat < f + (1 + pageOverflow pg))) ∧
    (∀ s, f ≤ s → s < f + (1 + pageOverflow pg) → ¬ coversSlot C.pages s ∧
      s ∈ pendSlots fl ∧ W64 (s : Int) ∉ fl.free ∧
        ∀ t pd, fl.pending !! t = some pd → W64 (s : Int) ∈ pd.ids → t = wtx) ∧
    (∀ x ∈ fl.free, x ∈ flIds pg) ∧ (∀ x, committedPending fl C x → x ∈ flIds pg) ∧
    (∀ x ∈ flIds pg, committedPending fl C x ∨
      (x.toNat < C.hwm ∧ x.toNat < 2 ^ 62 ∧ ¬ coversSlot C.pages x.toNat)) ∧
    (∀ a, fl.allocs !! W64 (f : Int) = some a → a.toNat ≤ C.txid) ∧
    pageId pg = f

/-- The synced freelist page's clause of `wdbOK'`: `flCurOK`, or with the flag `flCurOKr` for the
writer's txid. -/
def flClause : Bool → WDb → Prop
  | false, w => ∀ f, w.C.flpg = some f → flCurOK w.fl w.C (extentBytes w.wb f)
  | true, w => ∀ f, w.C.flpg = some f →
      16 ≤ (w.wb f).length ∧ flCurOKr w.fl w.C w.wtxid (extentBytes w.wb f)

/-- **The writer side's facts, flagged** (`wdbOK` but its synced-freelist-page clause,
`flClause fr`). -/
def wdbOK' (fr : Bool) (w : WDb) : Prop :=
  (∀ b l, w.ms = some (b, l) → w.m.maps = GMap.singleton b l) ∧
  (w.ms = none → w.m.maps = ∅ ∨ ∃ jb jl, w.junk = some (jb, jl) ∧
    w.m.maps = GMap.singleton jb jl) ∧
  w.C.hwm * 4096 ≤ w.m.size ∧
  (∀ s, s ∈ w.W ↔ 2 ≤ s ∧ s < max (mapLen w.ms) w.m.size / 4096 ∧ s ∉ treeSlots w.C ∧
    s ∉ pendSlots w.fl) ∧
  (∀ x ∈ w.fl.free, x.toNat ∉ treeSlots w.C) ∧
  flClause fr w ∧
  w.C.txid + 1 < 2 ^ 64 ∧ w.C.hwm < 2 ^ 64 ∧
  (∀ b l, w.ms = some (b, l) → w.C.hwm * 4096 ≤ l) ∧
  (∀ b l, w.ms = some (b, l) → l ≤ 0x1000000 → w.m.size ≤ l) ∧
  (∀ s, s ∈ treeSlots w.C ∨ s ∈ pendSlots w.fl → s < w.C.hwm) ∧
  (∀ x ∈ w.fl.free, x.toNat < w.C.hwm) ∧
  w.m.size < 2 ^ 63 ∧
  (∀ b l, w.ms = some (b, l) → w.m.size ≤ l ∨ w.m.size % 4096 = 0) ∧
  (∀ s ∈ w.W, 4096 * (s + 1) ≤ w.m.size → (w.wb s).length = 4096) ∧
  (∀ s, 4096 * s < w.m.size → w.m.size < 4096 * (s + 1) → w.m.size - 4096 * s ≤ (w.wb s).length) ∧
  0 ≤ w.fd.toInt

/-- `wdbOK' false` is `wdbOK` (by definition). -/
theorem wdbOK'_false (w : WDb) : wdbOK' false w ↔ wdbOK w := Iff.rfl

/-- `wdbOK` gives `wdbOK' false` (by definition; not `wdbOK' true`, whose synced page's slots
are pending). -/
theorem wdbOK_wdbOK' (w : WDb) (h : wdbOK w) : wdbOK' false w := h

/-- **The writer side with no synced freelist page** (a device: every clause of `wdbOK'` but
`flClause` holds of `w.noFl` as of `w`, and `flClause false` holds of it vacuously, so a lemma
stated over `wdbOK` that does not read the freelist page's clause applies to `wdbOK' fr`,
`wdbOK'_noFl`/`wdbOK'_of_noFl`). -/
def WDb.noFl (w : WDb) : WDb := { w with C := { w.C with flpg := none } }

/-- `wdbOK' fr w` gives `wdbOK` of `w.noFl`. -/
theorem wdbOK'_noFl (fr : Bool) (w : WDb) (h : wdbOK' fr w) : wdbOK w.noFl := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := h
  refine ⟨a1, a2, a3, a4, a5, fun f hf => ?_, a7⟩
  simp [WDb.noFl] at hf

/-- `wdbOK` of `w.noFl` and the freelist page's clause give `wdbOK' fr w`. -/
theorem wdbOK'_of_noFl (fr : Bool) (w : WDb) (h : wdbOK w.noFl) (hc : flClause fr w) :
    wdbOK' fr w := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := h
  exact ⟨a1, a2, a3, a4, a5, hc, a7⟩

/-- The freelist page's clause of `wdbOK' fr w`. -/
theorem wdbOK'_flClause (fr : Bool) (w : WDb) (h : wdbOK' fr w) : flClause fr w :=
  h.2.2.2.2.2.1

/-- `flClause` reads only the committed state, the freelist and the slots' bytes. -/
theorem flClause_congr (fr : Bool) (w w' : WDb) (hC : w'.C = w.C) (hfl : w'.fl = w.fl)
    (hwb : w'.wb = w.wb) (h : flClause fr w) : flClause fr w' := by
  cases fr
  · simp only [flClause] at h ⊢; rw [hC, hfl, hwb]; exact h
  · simp only [flClause, WDb.wtxid] at h ⊢; rw [hC, hfl, hwb]; exact h

/-- **`flClause` after a freelist allocation** (`FLPg.alloc`: free ids removed, the pending ids
kept, `allocs` given the run's first id `r`, which is free, so not the synced page's). -/
theorem flClause_alloc (fr : Bool) (w : WDb) (txid r : w64) (n : Nat) (hr : r ∈ w.fl.free)
    (h : flClause fr w) :
    flClause fr { w with fl := w.fl.alloc txid r n } := by
  have hsub : ∀ x, x ∈ (w.fl.alloc txid r n).allIds → x ∈ w.fl.allIds := by
    intro x hm
    simp only [FLPg.allIds, List.mem_append] at hm ⊢
    rcases hm with hm | hm
    · exact .inl ((List.mem_filter.1 hm).1)
    · exact .inr hm
  have hal : ∀ f : Nat, W64 (f : Int) ∉ w.fl.free → ∀ a,
      (w.fl.alloc txid r n).allocs !! W64 (f : Int) = some a → w.fl.allocs !! W64 (f : Int) = some a := by
    intro f hf a ha
    have hne : r ≠ W64 (f : Int) := fun e => hf (e ▸ hr)
    simp only [FLPg.alloc] at ha
    rwa [GMap.lookup_insert_ne _ _ hne] at ha
  cases fr
  · intro f hf
    intro f' hf'
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := h f hf f' hf'
    have hff : f' = f := Option.some.inj (hf'.symm.trans hf)
    subst hff
    have hnf : W64 (f' : Int) ∉ w.fl.free := fun hm =>
      (c9 f' (Nat.le_refl _) (by omega)).2 (List.mem_append_left _ hm)
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8,
      fun s a b => ⟨(c9 s a b).1, fun hm => (c9 s a b).2 (hsub _ hm)⟩,
      fun x hx => c10 x ((List.mem_filter.1 hx).1), fun x hx => c11 x hx, fun x hx => c12 x hx,
      fun a ha => c13 a (hal f' hnf a ha), c14⟩
  · intro f hf
    refine ⟨(h f hf).1, ?_⟩
    intro f' hf'
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := (h f hf).2 f' hf'
    have hff : f' = f := Option.some.inj (hf'.symm.trans hf)
    subst hff
    have hnf : W64 (f' : Int) ∉ w.fl.free := (c9 f' (Nat.le_refl _) (by omega)).2.2.1
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, fun s a b => ?_,
      fun x hx => c10 x ((List.mem_filter.1 hx).1), fun x hx => c11 x hx, fun x hx => c12 x hx,
      fun a ha => c13 a (hal f' hnf a ha), c14⟩
    obtain ⟨d1, d2, d3, d4⟩ := c9 s a b
    exact ⟨d1, d2, fun hm => d3 ((List.mem_filter.1 hm).1), d4⟩

/-- **The freed freelist page's recorded bytes are the writer side's** (maintainer 11, for the
flagged rollback): a slot of the synced page's extent that is pending is pending because the
writer freed the page (the page's id is in the writer's pending entry: `fbCond`), and the bytes
`F` recorded at the free (`store_free_fl`'s `fbRec`) are `w.wb`'s there. Vacuous under `wdbOK`
(no slot of the extent is pending: `fbRel_of_wdbOK`). -/
def fbRel (w : WDb) (F : GMap Nat (List w8)) : Prop :=
  ∀ f, w.C.flpg = some f → ∀ s, f ≤ s → s < f + (1 + pageOverflow (w.wb f)) →
    s ∈ pendSlots w.fl →
    (∃ pd, w.fl.pending !! w.wtxid = some pd ∧ ∃ x ∈ pd.ids, x.toNat = f) ∧
    F !! s = some (w.wb s)

/-- `fbRel` reads only the committed state, the freelist's pending entries and the slots' bytes. -/
theorem fbRel_congr (w w' : WDb) (F : GMap Nat (List w8)) (hC : w'.C = w.C)
    (hp : w'.fl.pending = w.fl.pending) (hwb : w'.wb = w.wb) (h : fbRel w F) : fbRel w' F := by
  have hps : pendSlots w'.fl = pendSlots w.fl := by
    simp only [pendSlots, FLPg.pendingIds, hp]
  intro f hf s h1 h2 hs
  rw [hC] at hf
  rw [hwb] at h2 ⊢
  rw [hps] at hs
  have := h f hf s h1 h2 hs
  simp only [WDb.wtxid, hC, hp] at this ⊢
  exact this

/-- Under `wdbOK` no slot of the synced page's extent is pending: `fbRel` holds of any `F`. -/
theorem fbRel_of_wdbOK (w : WDb) (hok : wdbOK w) (F : GMap Nat (List w8)) : fbRel w F := by
  intro f hf s h1 h2 hs
  exfalso
  have h16 := wb_header w hok f hf
  have hov : pageOverflow (extentBytes w.wb f) = pageOverflow (w.wb f) := by
    unfold pageOverflow pageHdr bytesAt
    congr 3
    unfold extentBytes
    rw [show 1 + pageOverflow (w.wb f) = (pageOverflow (w.wb f)) + 1 by omega, List.range'_succ,
      List.flatMap_cons, List.drop_zero, List.drop_zero,
      List.take_append_of_le_length h16]
  obtain ⟨-, -, -, -, -, c6, -⟩ := hok
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := c6 f hf f hf
  have hn := (h9 s h1 (by rw [hov]; exact h2)).2
  apply hn
  simp only [pendSlots, List.mem_map] at hs
  obtain ⟨x, hx, rfl⟩ := hs
  have : W64 (x.toNat : Int) = x := BitVec.eq_of_toNat_eq (toNat_W64_of_lt x.toNat x.isLt)
  rw [this]
  exact List.mem_append_right _ hx

/-- An allocation keeps `fbRel` (it keeps the pending entries). -/
theorem fbRel_alloc (w : WDb) (F : GMap Nat (List w8)) (txid r : w64) (n : Nat) (h : fbRel w F) :
    fbRel { w with fl := w.fl.alloc txid r n } F :=
  fbRel_congr w _ F rfl rfl rfl h

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The writer's database side in `Commit`, flagged**: `wdbW` with `wdbOK' fr` and the writer's
`fbTok` for the store's writer state `wLive v w.C` (its txid and publish flag are what `fbTok`
reads). -/
def wdbW' (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) : IProp GF :=
  iprop(wdbLive K.B K.db K.p K.sp K.t0 tx (wLive v w.C) w ∗
    ⌜wdbOK' fr w ∧ w.ms = some (v.base, mapLen w.ms) ∧ v = View.ofC v.base w.C⌝ ∗
    ∃ F : GMap Nat (List w8), fbTok K.B w.C w.fl (wLive v w.C) F ∗ ⌜fbRel w F⌝)

/-- `wdbW` is `wdbW' false`, with no recorded bytes (`fbTok_of_wdbOK`). -/
theorem wdbW_wdbW' (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ wdbW' false K tx v w := by
  unfold wdbW wdbW'
  iintro ⟨H, %h⟩
  iframe H
  isplitr
  · ipureintro; exact ⟨wdbOK_wdbOK' w h.1, h.2⟩
  iexists ∅
  isplitl
  · iapply (fbTok_of_wdbOK K.B w h.1 (wLive v w.C) ∅)
  · ipureintro; exact fbRel_of_wdbOK w h.1 ∅

/-- `wdbW' false` is `wdbW` (its token dropped: under `wdbOK` it is empty). -/
theorem wdbW'_wdbW (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW' (GF := GF) false K tx v w ⊢ wdbW K tx v w := by
  unfold wdbW wdbW'
  iintro ⟨H, %h, -⟩
  iframe H
  ipureintro; exact h

/-- The pure facts of `wdbW'`. -/
theorem wdbW'_ok (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW' (GF := GF) fr K tx v w ⊢
      wdbW' fr K tx v w ∗ ⌜wdbOK' fr w ∧ w.ms = some (v.base, mapLen w.ms) ∧
        v = View.ofC v.base w.C⌝ := by
  unfold wdbW'
  iintro ⟨H, %h, Ht⟩
  iframe H Ht
  isplitr
  · ipureintro; exact h
  · ipureintro; exact h

/-- **The writer's next txid does not wrap** (maintainer 12, item 1): the receipts of `wdbLive`
and the core's bounds (`isBoltCoreP_txid_lt`). For `Commit`'s `htx63`. -/
theorem wdbW'_txid_lt (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) :
    K.core (GF := GF) ∗ wdbW' fr K tx v w ⊢ wdbW' fr K tx v w ∗ ⌜w.C.txid + 1 < 2 ^ 63⌝ := by
  unfold wdbW' wdbLive BC.core
  iintro ⟨Hc, ⟨Hg, Hfl, Hsp, Hr⟩, Hok, Ht⟩
  icases isBoltCoreP_txid_lt K.B K.N K.db K.p K.sp K.t0 w.C.txid $$ [Hc Hr] with ⟨Hr, %h⟩
  · iframe
  iframe
  ipureintro; exact h

/-- `wdbW'_txid_lt` for `wdbW`. -/
theorem wdbW_txid_lt (K : BC) (tx : Loc) (v : View) (w : WDb) :
    K.core (GF := GF) ∗ wdbW K tx v w ⊢ wdbW K tx v w ∗ ⌜w.C.txid + 1 < 2 ^ 63⌝ := by
  unfold wdbW wdbLive BC.core
  iintro ⟨Hc, ⟨Hg, Hfl, Hsp, Hr⟩, Hok⟩
  icases isBoltCoreP_txid_lt K.B K.N K.db K.p K.sp K.t0 w.C.txid $$ [Hc Hr] with ⟨Hr, %h⟩
  · iframe
  iframe
  ipureintro; exact h

/-- **The writer's database side after a failed remap, flagged** (`wdbLost` with `wdbOK' fr` and
the writer's `fbTok`). -/
def wdbLost' (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) : IProp GF :=
  iprop(wdbLive K.B K.db K.p K.sp K.t0 tx (some v, some (w.C.txid + 1), false, false) w ∗
    ⌜wdbOK' fr w ∧ w.ms = none⌝ ∗
    ∃ F : GMap Nat (List w8), fbTok K.B w.C w.fl (some v, some (w.C.txid + 1), false, false) F ∗
      ⌜fbRel w F⌝)

/-- `wdbLost` is `wdbLost' false`, with no recorded bytes. -/
theorem wdbLost_wdbLost' (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbLost (GF := GF) K tx v w ⊢ wdbLost' false K tx v w := by
  unfold wdbLost wdbLost'
  iintro ⟨H, %h⟩
  iframe H
  isplitr
  · ipureintro; exact ⟨wdbOK_wdbOK' w h.1, h.2⟩
  iexists ∅
  isplitl
  · iapply (fbTok_of_wdbOK K.B w h.1 _ ∅)
  · ipureintro; exact fbRel_of_wdbOK w h.1 ∅

/-- `wdbLost' false` is `wdbLost` (its token dropped). -/
theorem wdbLost'_wdbLost (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbLost' (GF := GF) false K tx v w ⊢ wdbLost K tx v w := by
  unfold wdbLost wdbLost'
  iintro ⟨H, %h, -⟩
  iframe H
  ipureintro; exact h

/-- **A write transaction ready to close, flagged** (maintainer 11): `wtxEnd` with `wdbOK' fr` in
place of `wdbOK`, and the writer's `fbTok` for the store's writer state `ws` (with `fbRel`: after
`Commit`'s free of the synced freelist page, `store_rollback` returns the page's bytes through it).
`wtxEnd_wtxEnd'`, `wtxEnd'_wtxEnd` (flag `false`). -/
def wtxEnd' (fr : Bool) (K : BC) (tx : Loc) (r : TxReg) (X : WX) (ws : WSt) (w : WDb) :
    IProp GF :=
  iprop(K.full ∗ (wtxW K tx r false X ∨ wtxLost K tx r false X) ∗
    wdbLive K.B K.db K.p K.sp K.t0 tx ws w ∗ sync.ownMutex K.db.[DB, go!"rwlock"] ∗
    ghostVar K.B.cls (1 : Qp).half false ∗
    (∃ c : TxViewC, ghostVar r.n.v 1 (c, TxX.wr X)) ∗
    ghostVar K.B.st (1 : Qp).half.half (treeData w.C) ∗
    ⌜wdbOK' fr w ∧ X.t.t.writable' = true ∧ (X.t.bs !! X.rl).isSome⌝ ∗
    ∃ F : GMap Nat (List w8), fbTok K.B w.C w.fl ws F ∗ ⌜fbRel w F⌝)

/-- `wtxEnd` is `wtxEnd' false`, with no recorded bytes. -/
theorem wtxEnd_wtxEnd' (K : BC) (tx : Loc) (r : TxReg) (X : WX) (ws : WSt) (w : WDb) :
    wtxEnd (GF := GF) K tx r X ws w ⊢ wtxEnd' false K tx r X ws w := by
  unfold wtxEnd wtxEnd'
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, %h⟩
  iframe H1 H2 H3 H4 H5 H6 H7
  isplitr
  · ipureintro; exact ⟨wdbOK_wdbOK' w h.1, h.2⟩
  iexists ∅
  isplitl
  · iapply (fbTok_of_wdbOK K.B w h.1 ws ∅)
  · ipureintro; exact fbRel_of_wdbOK w h.1 ∅

/-- `wtxEnd' false` is `wtxEnd` (its token dropped). -/
theorem wtxEnd'_wtxEnd (K : BC) (tx : Loc) (r : TxReg) (X : WX) (ws : WSt) (w : WDb) :
    wtxEnd' (GF := GF) false K tx r X ws w ⊢ wtxEnd K tx r X ws w := by
  unfold wtxEnd wtxEnd'
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, %h, -⟩
  iframe H1 H2 H3 H4 H5 H6 H7
  ipureintro; exact h

omit [GooseSemantics] go_gctx hos sem in
/-- `fbTok` reads only the writer state's txid and publish flag. -/
theorem fbTok_ws (B : BNs) (C : CommitSt) (fl : FLPg) (ws ws' : WSt) (F : GMap Nat (List w8))
    (h1 : ws'.2.1 = ws.2.1) (h2 : ws'.2.2.1 = ws.2.2.1) :
    fbTok (GF := GF) B C fl ws F ⊢ fbTok B C fl ws' F := by
  unfold fbTok; rw [h1, h2]

omit [GooseSemantics] go_gctx hos sem in
/-- `fbTok` reads only the freelist's pending ids: an allocation keeps it. -/
theorem fbTok_alloc (B : BNs) (C : CommitSt) (fl : FLPg) (ws : WSt) (F : GMap Nat (List w8))
    (txid r : w64) (n : Nat) :
    fbTok (GF := GF) B C fl ws F ⊢ fbTok B C (fl.alloc txid r n) ws F := .rfl

end res

end bbolt
end EtcdGrove
end Perennial
