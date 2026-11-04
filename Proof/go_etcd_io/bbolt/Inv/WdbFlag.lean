/-
**The flagged writer side** (batch 44.1 of `notes/bbolt-proof-plan.md`, U10g's finding, decided by
the coordinator): between `Commit`'s free of the old synced freelist page (`store_free_fl`) and the
publish or rollback, the page's own slots are pending for the writer's txid, which `flCurOK`'s
slot clause forbids. `wdbOK' true` relaxes that clause only (`flCurOKr`: a slot of the synced
page's extent may be pending, for the writer's txid only); `wdbOK' false` is `wdbOK`
(`wdbOK'_false`, by definition). `wdbW' fr` is `wdbW` with `wdbOK' fr` and the writer's
`fbTok` (the freed page's recorded bytes' half, which `store_publish` and `store_rollback` take):
`wdbW_wdbW'` (any flag, the token empty), `wdbW'_wdbW` (flag `false`, the token dropped).
Existing statements keep `wdbOK`/`wdbW`; the steps of `Commit` from the free on take the flagged
form.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **`flCurOK` with its slot clause relaxed** for the writer `wtx`: a slot of the synced page's
extent is not covered, and is not free and is pending only for `wtx` (in place of "in no list").
Every other clause is `flCurOK`'s. -/
def flCurOKr (fl : FLPg) (C : CommitSt) (wtx : w64) (pg : List w8) : Prop :=
  ∀ f, C.flpg = some f →
    2 ≤ f ∧ f + (1 + pageOverflow pg) ≤ C.hwm ∧ pg.length = (1 + pageOverflow pg) * 4096 ∧
    pageFlags pg = freelistPageFlag ∧
    16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length ∧
    (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ x.toNat) ∧
    (∀ x ∈ flIds pg, ¬ (f ≤ x.toNat ∧ x.toNat < f + (1 + pageOverflow pg))) ∧
    (∀ s, f ≤ s → s < f + (1 + pageOverflow pg) → ¬ coversSlot C.pages s ∧
      (W64 (s : Int) ∉ fl.allIds ∨ (W64 (s : Int) ∉ fl.free ∧
        ∀ t pd, fl.pending !! t = some pd → W64 (s : Int) ∈ pd.ids → t = wtx))) ∧
    (∀ x ∈ fl.free, x ∈ flIds pg) ∧ (∀ x, committedPending fl C x → x ∈ flIds pg) ∧
    (∀ x ∈ flIds pg, committedPending fl C x ∨
      (x.toNat < C.hwm ∧ x.toNat < 2 ^ 62 ∧ ¬ coversSlot C.pages x.toNat))

theorem flCurOK_flCurOKr (fl : FLPg) (C : CommitSt) (wtx : w64) (pg : List w8)
    (h : flCurOK fl C pg) : flCurOKr fl C wtx pg := by
  intro f hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h f hf
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun s a b => ⟨(h9 s a b).1, .inl (h9 s a b).2⟩, h10, h11,
    h12⟩

/-- The synced freelist page's clause of `wdbOK'`: `flCurOK`, or with the flag `flCurOKr` for the
writer's txid. -/
def flClause : Bool → WDb → Prop
  | false, w => ∀ f, w.C.flpg = some f → flCurOK w.fl w.C (extentBytes w.wb f)
  | true, w => ∀ f, w.C.flpg = some f → flCurOKr w.fl w.C w.wtxid (extentBytes w.wb f)

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
  (∀ s ∈ w.W, 4096 * (s + 1) ≤ w.m.size → (w.wb s).length = 4096)

/-- `wdbOK' false` is `wdbOK` (by definition). -/
theorem wdbOK'_false (w : WDb) : wdbOK' false w ↔ wdbOK w := Iff.rfl

/-- `wdbOK` gives `wdbOK'` at either flag. -/
theorem wdbOK_wdbOK' (fr : Bool) (w : WDb) (h : wdbOK w) : wdbOK' fr w := by
  cases fr
  · exact h
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
    exact ⟨a1, a2, a3, a4, a5,
      fun f hf => flCurOK_flCurOKr _ _ _ _ (a6 f hf), a7⟩

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
    ∃ F : GMap Nat (List w8), fbTok K.B w.C w.fl (wLive v w.C) F)

/-- `wdbW` is `wdbW'` at either flag, with no recorded bytes (`fbTok_of_wdbOK`). -/
theorem wdbW_wdbW' (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ wdbW' fr K tx v w := by
  unfold wdbW wdbW'
  iintro ⟨H, %h⟩
  iframe H
  isplitr
  · ipureintro; exact ⟨wdbOK_wdbOK' fr w h.1, h.2⟩
  iexists ∅
  iapply (fbTok_of_wdbOK K.B w h.1 (wLive v w.C) ∅)

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

end res

end bbolt
end EtcdGrove
end Perennial
