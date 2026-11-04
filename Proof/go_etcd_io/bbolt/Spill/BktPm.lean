/-
`Bucket.spill`'s root loop (U9n, `notes/bbolt-proof-plan.md`; pure): **the page cache and a
bucket's positions**. The spill's global state (`spG`) keeps the page cache's ids those of the
buffers, none a view page; so the transaction's page cache holds no view page (`pmFresh`:
`Cursor.seek_w`'s premise after the spill allocated), and a bucket whose logical tree is finite
(`rtOK`) and clean, with a root page, has every position a view page, so none in the page cache
(`Bucket.free`'s premise for an inlineable child freed after an earlier sibling's spill allocated:
batch 37 item 20, no change of the premise needed).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeSteps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section pm
variable [GooseExts]

/-- **The page cache holds no view page** during the spill. -/
theorem pmFresh_of_spG {X : WX} {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X txid ml fl) :
    pmFresh X := by
  intro id hid
  have hb := (hG.2.2.2.2.2.1 id).1 hid
  exact (hG.2.2.2.2.2.2.2 id hb).2.2

/-- A view page is not in the page cache during the spill. -/
theorem pm_none_of_view {X : WX} {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X txid ml fl)
    {id : w64} (hv : (X.v.pages !! id.toNat).isSome) : X.t.pm !! id = none := by
  cases hp : X.t.pm !! id with
  | none => rfl
  | some p =>
    have := pmFresh_of_spG hG id (by rw [hp]; rfl)
    rw [this] at hv; cases hv

/-- The root position of a tree of `L` is in `L`. -/
theorem ltIs_isSome {L : LTree} {bl : Loc} (s : RTree) (h : ltIs L bl s) : (L bl s.pid).isSome := by
  cases s with
  | mk p lf ws cs =>
    cases lf <;> simp only [ltIs] at h <;> simp [RTree.pid, h.1]

/-- **Every position of a finite logical tree is in it.** -/
theorem positions_ltree {X : WX} {bl : Loc} (hrt : rtOK X bl) :
    ∀ p ∈ X.positions bl, (ltree X bl p).isSome := by
  obtain ⟨t, ht, hp, hh, -⟩ := hrt
  intro p hpos
  rw [show X.positions bl = t.pos by
    unfold WX.positions; rw [← hp]; exact lposF_ltIs (ltree X) bl t X.fuel ht hh] at hpos
  obtain ⟨s, hs, rfl⟩ := RTree.pos_subs t p hpos
  exact ltIs_isSome s (ltIs_subs (ltree X) bl t s ht hs)

/-- **Every position of a clean bucket with a root page is a view page** (its logical tree finite). -/
theorem positions_view {X : WX} {hwm : Nat} {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B)
    (hc : bktClean X.v hwm bl B) (h0 : B.ib.root' ≠ W64 0) (hrt : rtOK X bl) :
    ∀ p ∈ X.positions bl, (X.v.pages !! p.toNat).isSome := by
  intro p hp
  have hs := positions_ltree hrt p hp
  unfold ltree at hs
  rw [hB] at hs
  simp only at hs
  cases hres : resolve B p with
  | some l =>
    rw [hres] at hs
    have hnm : B.nm !! p = some l := by unfold resolve at hres; rwa [if_neg h0] at hres
    obtain ⟨-, r, hr, hpg⟩ := hc.2.2.2.2.1 p l hnm
    have hwf := (hc.2.2.2.2.2.2.2.1 l r hr).2.2.2.2.2.2.2.2.2.1 h0
    rw [hpg] at hwf
    cases hwf with
    | page _ pg _ _ hpg' _ _ _ => rw [hpg']; rfl
  | none =>
    rw [hres] at hs
    simp only [Option.isSome_map] at hs
    unfold wpageAt at hs
    rw [if_neg h0] at hs
    simpa using hs

/-- **`Bucket.free`'s page-cache premise during the spill** (batch 37 item 20): a clean bucket
with a root page and a finite logical tree has no position in the page cache. -/
theorem positions_pm_none {X : WX} {txid : w64} {ml : Nat} {fl : FLPg} {hwm : Nat} {bl : Loc}
    {B : BRec} (hG : spG X txid ml fl) (hB : X.t.bs !! bl = some B) (hc : bktClean X.v hwm bl B)
    (h0 : B.ib.root' ≠ W64 0) (hrt : rtOK X bl) :
    ∀ pid ∈ X.positions bl, X.t.pm !! pid = none :=
  fun pid hp => pm_none_of_view hG (positions_view hB hc h0 hrt pid hp)

end pm

end Spill

end bbolt
end EtcdGrove
end Perennial
